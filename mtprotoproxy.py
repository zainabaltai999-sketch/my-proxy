#!/usr/bin/env python3

import asyncio
import socket
import urllib.parse
import urllib.request
import collections
import time
import datetime
import hmac
import base64
import hashlib
import random
import binascii
import sys
import re
import runpy
import signal
import os
import stat
import traceback


TG_DATACENTER_PORT = 443

TG_DATACENTERS_V4 = [
    "149.154.175.50", "149.154.167.51", "149.154.175.100",
    "149.154.167.91", "149.154.171.5"
]

TG_DATACENTERS_V6 = [
    "2001:b28:f23d:f001::a", "2001:67c:04e8:f002::a", "2001:b28:f23d:f003::a",
    "2001:67c:04e8:f004::a", "2001:b28:f23f:f005::a"
]

# This list will be updated in the runtime
TG_MIDDLE_PROXIES_V4 = {
    1: [("149.154.175.50", 8888)], -1: [("149.154.175.50", 8888)],
    2: [("149.154.161.144", 8888)], -2: [("149.154.161.144", 8888)],
    3: [("149.154.175.100", 8888)], -3: [("149.154.175.100", 8888)],
    4: [("91.108.4.136", 8888)], -4: [("149.154.165.109", 8888)],
    5: [("91.108.56.183", 8888)], -5: [("91.108.56.183", 8888)]
}

TG_MIDDLE_PROXIES_V6 = {
    1: [("2001:b28:f23d:f001::d", 8888)], -1: [("2001:b28:f23d:f001::d", 8888)],
    2: [("2001:67c:04e8:f002::d", 80)], -2: [("2001:67c:04e8:f002::d", 80)],
    3: [("2001:b28:f23d:f003::d", 8888)], -3: [("2001:b28:f23d:f003::d", 8888)],
    4: [("2001:67c:04e8:f004::d", 8888)], -4: [("2001:67c:04e8:f004::d", 8888)],
    5: [("2001:b28:f23f:f005::d", 8888)], -5: [("2001:b28:f23f:f005::d", 8888)]
}

PROXY_SECRET = bytes.fromhex(
    "c4f9faca9678e6bb48ad6c7e2ce5c0d24430645d554addeb55419e034da62721" +
    "d046eaab6e52ab14a95a443ecfb3463e79a05a66612adf9caeda8be9a80da698" +
    "6fb0a6ff387af84d88ef3a6413713e5c3377f6e1a3d47d99f5e0c56eece8f05c" +
    "54c490b079e31bef82ff0ee8f2b0a32756d249c5f21269816cb7061b265db212"
)

SKIP_LEN = 8
PREKEY_LEN = 32
KEY_LEN = 32
IV_LEN = 16
HANDSHAKE_LEN = 64
PROTO_TAG_POS = 56
DC_IDX_POS = 60

MIN_CERT_LEN = 1024

PROTO_TAG_ABRIDGED = b"\xef\xef\xef\xef"
PROTO_TAG_INTERMEDIATE = b"\xee\xee\xee\xee"
PROTO_TAG_SECURE = b"\xdd\xdd\xdd\xdd"

CBC_PADDING = 16
PADDING_FILLER = b"\x04\x00\x00\x00"

MIN_MSG_LEN = 12
MAX_MSG_LEN = 2 ** 24

STAT_DURATION_BUCKETS = [0.1, 0.5, 1, 2, 5, 15, 60, 300, 600, 1800, 2**31 - 1]

my_ip_info = {"ipv4": None, "ipv6": None}
used_handshakes = collections.OrderedDict()
client_ips = collections.OrderedDict()
last_client_ips = {}
disable_middle_proxy = False
is_time_skewed = False
fake_cert_len = random.randrange(1024, 4096)
mask_host_cached_ip = None
last_clients_with_time_skew = {}
last_clients_with_same_handshake = collections.Counter()
proxy_start_time = 0
proxy_links = []

stats = collections.Counter()
user_stats = collections.defaultdict(collections.Counter)

config = {}


def init_config():
    global config
    # we use conf_dict to protect the original config from exceptions when reloading
    if len(sys.argv) < 2:
        conf_dict = runpy.run_module("config")
    elif len(sys.argv) == 2:
        # launch with own config
        conf_dict = runpy.run_path(sys.argv[1])
    else:
        # undocumented way of launching
        conf_dict = {}
        conf_dict["PORT"] = int(sys.argv[1])
        secrets = sys.argv[2].split(",")
        conf_dict["USERS"] = {"user%d" % i: secrets[i].zfill(32) for i in range(len(secrets))}
        conf_dict["MODES"] = {"classic": False, "secure": True, "tls": True}
        if len(sys.argv) > 3:
            conf_dict["AD_TAG"] = sys.argv[3]
        if len(sys.argv) > 4:
            conf_dict["TLS_DOMAIN"] = sys.argv[4]
            conf_dict["MODES"] = {"classic": False, "secure": False, "tls": True}

    conf_dict = {k: v for k, v in conf_dict.items() if k.isupper()}

    conf_dict.setdefault("PORT", 3256)
    conf_dict.setdefault("USERS", {"tg":  "00000000000000000000000000000000"})
    conf_dict["AD_TAG"] = bytes.fromhex(conf_dict.get("AD_TAG", ""))

    for user, secret in conf_dict["USERS"].items():
        if not re.fullmatch("[0-9a-fA-F]{32}", secret):
            fixed_secret = re.sub(r"[^0-9a-fA-F]", "", secret).zfill(32)[:32]

            print_err("Bad secret for user %s, should be 32 hex chars, got %s. " % (user, secret))
            print_err("Changing it to %s" % fixed_secret)

            conf_dict["USERS"][user] = fixed_secret

    # load advanced settings

    # use middle proxy, necessary to show ad
    conf_dict.setdefault("USE_MIDDLE_PROXY", len(conf_dict["AD_TAG"]) == 16)

    # if IPv6 available, use it by default, IPv6 with middle proxies is unstable now
    conf_dict.setdefault("PREFER_IPV6", socket.has_ipv6 and not conf_dict["USE_MIDDLE_PROXY"])

    # disables tg->client traffic reencryption, faster but less secure
    conf_dict.setdefault("FAST_MODE", True)

    # enables some working modes
    modes = conf_dict.get("MODES", {})

    if "MODES" not in conf_dict:
        modes.setdefault("classic", True)
        modes.setdefault("secure", True)
        modes.setdefault("tls", True)
    else:
        modes.setdefault("classic", False)
        modes.setdefault("secure", False)
        modes.setdefault("tls", False)

    legacy_warning = False
    if "SECURE_ONLY" in conf_dict:
        legacy_warning = True
        modes["classic"] = not bool(conf_dict["SECURE_ONLY"])

    if "TLS_ONLY" in conf_dict:
        legacy_warning = True
        if conf_dict["TLS_ONLY"]:
            modes["classic"] = False
            modes["secure"] = False

    if not modes["classic"] and not modes["secure"] and not modes["tls"]:
        print_err("No known modes enabled, enabling tls-only mode")
        modes["tls"] = True

    if legacy_warning:
        print_err("Legacy options SECURE_ONLY or TLS_ONLY detected")
        print_err("Please use MODES in your config instead:")
        print_err("MODES = {")
        print_err('    "classic": %s,' % modes["classic"])
        print_err('    "secure": %s,' % modes["secure"])
        print_err('    "tls": %s' % modes["tls"])
        print_err("}")

    conf_dict["MODES"] = modes

    # accept incoming connections only with proxy protocol v1/v2, useful for nginx and haproxy
    conf_dict.setdefault("PROXY_PROTOCOL", False)

    # set the tls domain for the proxy, has an influence only on starting message
    conf_dict.setdefault("TLS_DOMAIN", "www.google.com")

    # enable proxying bad clients to some host
    conf_dict.setdefault("MASK", True)

    # the next host to forward bad clients
    conf_dict.setdefault("MASK_HOST", conf_dict["TLS_DOMAIN"])

    # set the home domain for the proxy, has an influence only on the log message
    conf_dict.setdefault("MY_DOMAIN", False)

    # the next host's port to forward bad clients
    conf_dict.setdefault("MASK_PORT", 443)

    # use upstream SOCKS5 proxy
    conf_dict.setdefault("SOCKS5_HOST", None)
    conf_dict.setdefault("SOCKS5_PORT", None)
    conf_dict.setdefault("SOCKS5_USER", None)
    conf_dict.setdefault("SOCKS5_PASS", None)

    if conf_dict["SOCKS5_HOST"] and conf_dict["SOCKS5_PORT"]:
        # Disable the middle proxy if using socks, they are not compatible
        conf_dict["USE_MIDDLE_PROXY"] = False

    # user tcp connection limits, the mapping from name to the integer limit
    # one client can create many tcp connections, up to 8
    conf_dict.setdefault("USER_MAX_TCP_CONNS", {})

    # expiration date for users in format of day/month/year
    conf_dict.setdefault("USER_EXPIRATIONS", {})
    for user in conf_dict["USER_EXPIRATIONS"]:
        expiration = datetime.datetime.strptime(conf_dict["USER_EXPIRATIONS"][user], "%d/%m/%Y")
        conf_dict["USER_EXPIRATIONS"][user] = expiration

    # the data quota for user
    conf_dict.setdefault("USER_DATA_QUOTA", {})

    # length of used handshake randoms for active fingerprinting protection, zero to disable
    conf_dict.setdefault("REPLAY_CHECK_LEN", 65536)

    # accept clients with bad clocks. This reduces the protection against replay attacks
    conf_dict.setdefault("IGNORE_TIME_SKEW", False)

    # length of last client ip addresses for logging
    conf_dict.setdefault("CLIENT_IPS_LEN", 131072)

    # delay in seconds between stats printing
    conf_dict.setdefault("STATS_PRINT_PERIOD", 600)

    # delay in seconds between middle proxy info updates
    conf_dict.setdefault("PROXY_INFO_UPDATE_PERIOD", 24*60*60)

    # delay in seconds between time getting, zero means disabled
    conf_dict.setdefault("GET_TIME_PERIOD", 10*60)

    # delay in seconds between getting the length of certificate on the mask host
    conf_dict.setdefault("GET_CERT_LEN_PERIOD", random.randrange(4*60*60, 6*60*60))

    # max socket buffer size to the client direction, the more the faster, but more RAM hungry
    # can be the tuple (low, users_margin, high) for the adaptive case. If no much users, use high
    conf_dict.setdefault("TO_CLT_BUFSIZE", (16384, 100, 131072))

    # max socket buffer size to the telegram servers direction, also can be the tuple
    conf_dict.setdefault("TO_TG_BUFSIZE", 65536)

    # keepalive period for clients in secs
    conf_dict.setdefault("CLIENT_KEEPALIVE", 10*60)

    # drop client after this timeout if the handshake fail
    conf_dict.setdefault("CLIENT_HANDSHAKE_TIMEOUT", random.randrange(5, 15))

    # if client doesn't confirm data for this number of seconds, it is dropped
    conf_dict.setdefault("CLIENT_ACK_TIMEOUT", 5*60)

    # telegram servers connect timeout in seconds
    conf_dict.setdefault("TG_CONNECT_TIMEOUT", 10)

    # drop connection if no data from telegram server for this many seconds
    conf_dict.setdefault("TG_READ_TIMEOUT", 60)

    # listen address for IPv4
    conf_dict.setdefault("LISTEN_ADDR_IPV4", "0.0.0.0")

    # listen address for IPv6
    conf_dict.setdefault("LISTEN_ADDR_IPV6", "::")

    # listen unix socket
    conf_dict.setdefault("LISTEN_UNIX_SOCK", "")

    # prometheus exporter listen port, use some random port here
    conf_dict.setdefault("METRICS_PORT", None)

    # prometheus listen addr ipv4
    conf_dict.setdefault("METRICS_LISTEN_ADDR_IPV4", "0.0.0.0")

    # prometheus listen addr ipv6
    conf_dict.setdefault("METRICS_LISTEN_ADDR_IPV6", None)

    # prometheus scrapers whitelist
    conf_dict.setdefault("METRICS_WHITELIST", ["127.0.0.1", "::1"])

    # export proxy link to prometheus
    conf_dict.setdefault("METRICS_EXPORT_LINKS", False)

    # default prefix for metrics
    conf_dict.setdefault("METRICS_PREFIX", "mtprotoproxy_")

    # allow access to config by attributes
    config = type("config", (dict,), conf_dict)(conf_dict)


def apply_upstream_proxy_settings():
    # apply socks settings in place
    if config.SOCKS5_HOST and config.SOCKS5_PORT:
        import socks
        print_err("Socket-proxy mode activated, it is incompatible with advertising and uvloop")
        socks.set_default_proxy(socks.PROXY_TYPE_SOCKS5, config.SOCKS5_HOST, config.SOCKS5_PORT,
                                username=config.SOCKS5_USER, password=config.SOCKS5_PASS)
        if not hasattr(socket, "origsocket"):
            socket.origsocket = socket.socket
            socket.socket = socks.socksocket
    elif hasattr(socket, "origsocket"):
        socket.socket = socket.origsocket
        del socket.origsocket


def try_use_cryptography_module():
    from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
    from cryptography.hazmat.backends import default_backend

    class CryptographyEncryptorAdapter:
        __slots__ = ('encryptor', 'decryptor')

        def __init__(self, cipher):
            self.encryptor = cipher.encryptor()
            self.decryptor = cipher.decryptor()

        def encrypt(self, data):
            return self.encryptor.update(data)

        def decrypt(self, data):
            return self.decryptor.update(data)

    def create_aes_ctr(key, iv):
        iv_bytes = int.to_bytes(iv, 16, "big")
        cipher = Cipher(algorithms.AES(key), modes.CTR(iv_bytes), default_backend())
        return CryptographyEncryptorAdapter(cipher)

    def create_aes_cbc(key, iv):
        cipher = Cipher(algorithms.AES(key), modes.CBC(iv), default_backend())
        return CryptographyEncryptorAdapter(cipher)

    return create_aes_ctr, create_aes_cbc


def try_use_pycrypto_or_pycryptodome_module():
    from Crypto.Cipher import AES
    from Crypto.Util import Counter

    def create_aes_ctr(key, iv):
        ctr = Counter.new(128, initial_value=iv)
        return AES.new(key, AES.MODE_CTR, counter=ctr)

    def create_aes_cbc(key, iv):
        return AES.new(key, AES.MODE_CBC, iv)

    return create_aes_ctr, create_aes_cbc


def use_slow_bundled_cryptography_module():
    import pyaes

    msg = "To make the program a *lot* faster, please install cryptography module: "
    msg += "pip install cryptography\n"
    print(msg, flush=True, file=sys.stderr)

    class BundledEncryptorAdapter:
        __slots__ = ('mode', )

        def __init__(self, mode):
            self.mode = mode

        def encrypt(self, data):
            encrypter = pyaes.Encrypter(self.mode, pyaes.PADDING_NONE)
            return encrypter.feed(data) + encrypter.feed()

        def decrypt(self, data):
            decrypter = pyaes.Decrypter(self.mode, pyaes.PADDING_NONE)
            return decrypter.feed(data) + decrypter.feed()

    def create_aes_ctr(key, iv):
        ctr = pyaes.Counter(iv)
        return pyaes.AESModeOfOperationCTR(key, ctr)

    def create_aes_cbc(key, iv):
        mode = pyaes.AESModeOfOperationCBC(key, iv)
        return BundledEncryptorAdapter(mode)
    return create_aes_ctr, create_aes_cbc


try:
    create_aes_ctr, create_aes_cbc = try_use_cryptography_module()
except ImportError:
    try:
        create_aes_ctr, create_aes_cbc = try_use_pycrypto_or_pycryptodome_module()
    except ImportError:
        create_aes_ctr, create_aes_cbc = use_slow_bundled_cryptography_module()


def print_err(*params):
    print(*params, file=sys.stderr, flush=True)


def ensure_users_in_user_stats():
    global user_stats

    for user in config.USERS:
        user_stats[user].update()


def init_proxy_start_time():
    global proxy_start_time
    proxy_start_time = time.time()


def update_stats(**kw_stats):
    global stats
    stats.update(**kw_stats)


def update_user_stats(user, **kw_stats):
    global user_stats
    user_stats[user].update(**kw_stats)


def update_durations(duration):
    global stats

    for bucket in STAT_DURATION_BUCKETS:
        if duration <= bucket:
            break

    update_stats(**{"connects_with_duration_le_%s" % str(bucket): 1})


def get_curr_connects_count():
    global user_stats

    all_connects = 0
    for user, stat in user_stats.items():
        all_connects += stat["curr_connects"]
    return all_connects


def get_to_tg_bufsize():
    if isinstance(config.TO_TG_BUFSIZE, int):
        return config.TO_TG_BUFSIZE

    low, margin, high = config.TO_TG_BUFSIZE
    return high if get_curr_connects_count() < margin else low


def get_to_clt_bufsize():
    if isinstance(config.TO_CLT_BUFSIZE, int):
        return config.TO_CLT_BUFSIZE

    low, margin, high = config.TO_CLT_BUFSIZE
    return high if get_curr_connects_count() < margin else low


class MyRandom(random.Random):
    def __init__(self):
        super().__init__()
        key = bytes([random.randrange(256) for i in range(32)])
        iv = random.randrange(256**16)

        self.encryptor = create_aes_ctr(key, iv)
        self.buffer = bytearray()

    def getrandbits(self, k):
        numbytes = (k + 7) // 8
        return int.from_bytes(self.getrandbytes(numbytes), 'big') >> (numbytes * 8 - k)

    def getrandbytes(self, n):
        CHUNK_SIZE = 512

        while n > len(self.buffer):
            data = int.to_bytes(super().getrandbits(CHUNK_SIZE*8), CHUNK_SIZE, "big")
            self.buffer += self.encryptor.encrypt(data)

        result = self.buffer[:n]
        self.buffer = self.buffer[n:]
        return bytes(result)


myrandom = MyRandom()


class TgConnectionPool:
    MAX_CONNS_IN_POOL = 16

    def __init__(self):
        self.pools = {}

    async def open_tg_connection(self, host, port, init_func=None):
        task = asyncio.open_connection(host, port, limit=get_to_clt_bufsize())
        reader_tgt, writer_tgt = await asyncio.wait_for(task, timeout=config.TG_CONNECT_TIMEOUT)

        set_keepalive(writer_tgt.get_extra_info("socket"))
        set_bufsizes(writer_tgt.get_extra_info("socket"), get_to_clt_bufsize(), get_to_tg_bufsize())

        if init_func:
            return await asyncio.wait_for(init_func(host, port, reader_tgt, writer_tgt),
                                          timeout=config.TG_CONNECT_TIMEOUT)
        return reader_tgt, writer_tgt

    def is_conn_dead(self, reader, writer):
        if writer.transport.is_closing():
            return True
        raw_reader = reader
        while hasattr(raw_reader, 'upstream'):
            raw_reader = raw_reader.upstream
        if raw_reader.at_eof():
            return True
        return False

    def register_host_port(self, host, port, init_func):
        if (host, port, init_func) not in self.pools:
            self.pools[(host, port, init_func)] = []

        while len(self.pools[(host, port, init_func)]) < TgConnectionPool.MAX_CONNS_IN_POOL:
            connect_task = asyncio.ensure_future(self.open_tg_connection(host, port, init_func))
            self.pools[(host, port, init_func)].append(connect_task)

    async def get_connection(self, host, port, init_func=None):
        self.register_host_port(host, port, init_func)

        ret = None
        for task in self.pools[(host, port, init_func)][:]:
            if task.done():
                if task.exception():
                    self.pools[(host, port, init_func)].remove(task)
                    continue

                reader, writer, *other = task.result()
                if self.is_conn_dead(reader, writer):
                    self.pools[(host, port, init_func)].remove(task)
                    writer.transport.abort()
                    continue

                if not ret:
                    self.pools[(host, port, init_func)].remove(task)
                    ret = (reader, writer, *other)

        self.register_host_port(host, port, init_func)
        if ret:
            return ret
        return await self.open_tg_connection(host, port, init_func)


tg_connection_pool = TgConnectionPool()


class LayeredStreamReaderBase:
    __slots__ = ("upstream", )

    def __init__(self, upstream):
        self.upstream = upstream

    async def read(self, n):
        return await self.upstream.read(n)

    async def readexactly(self, n):
        return await self.upstream.readexactly(n)


class LayeredStreamWriterBase:
    __slots__ = ("upstream", )

    def __init__(self, upstream):
        self.upstream = upstream

    def write(self, data, extra={}):
        return self.upstream.write(data)

    def write_eof(self):
        return self.upstream.write_eof()

    async def drain(self):
        return await self.upstream.drain()

    def close(self):
        return self.upstream.close()

    def abort(self):
        return self.upstream.transport.abort()

    def get_extra_info(self, name):
        return self.upstream.get_extra_info(name)

    @property
    def transport(self):
        return self.upstream.transport


class FakeTLSStreamReader(LayeredStreamReaderBase):
    __slots__ = ('buf', )

    def __init__(self, upstream):
        self.upstream = upstream
        self.buf = bytearray()

    async def read(self, n, ignore_buf=False):
        if self.buf and not ignore_buf:
            data = self.buf
            self.buf = bytearray()
            return bytes(data)

        while True:
            tls_rec_type = await self.upstream.readexactly(1)
            if not tls_rec_type:
                return b""

            if tls_rec_type not in [b"\x14", b"\x17"]:
                print_err("BUG: bad tls type %s in FakeTLSStreamReader" % tls_rec_type)
                return b""

            version = await self.upstream.readexactly(2)
            if vers
