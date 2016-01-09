import Crypto.Cipher.AES as AES
import Crypto.Util.Counter as AESCounter
from Crypto.Hash.HMAC import HMAC
import Crypto.Hash.SHA

from struct import pack,unpack
from bitstring import BitArray #pip install bitstring
from functools import partial, reduce
from base64 import b64decode
from binascii import a2b_hex, b2a_hex
import operator
import sys

class AuthenticationFailure(Exception): pass

#------------- BASIC BYTESTRING MANIPULATION OPERATIONS ----------------

if sys.version < "3.2":
    def int_to_bytes( i, n_bytes ):
        #converts a integer to n bytes (unsigned, big endian)
        return BitArray(uint=i, length=n_bytes*8).bytes

    def bytes_to_int( b ):
        return int( b2a_hex(b), 16)
else:
    def int_to_bytes( i, n_bytes ):
        return i.to_bytes( n_bytes, byteorder='big')

    def bytes_to_int( b ):
        return int.from_bytes( b, byteorder='big')

def zero_pad(s1,s2):
    #makes bytestrings the same size by zero padding the most significant bits
    swap= len(s1)>len(s2)
    if swap:
        s1,s2=s2,s1
    s1=s1.rjust( len(s2), b'\0' )
    if swap:
        s1,s2= s2,s1
    return s1,s2

def xor( *args ):
    '''xors two or more bytestrings'''
    size= max(map(len, args))
    args_int= map(bytes_to_int, args)
    result_ints= reduce(operator.xor, args_int)
    return int_to_bytes(result_ints, size)

def srtp_div(s1,s2):
    '''div (modulus) operation, as defined in https://tools.ietf.org/html/rfc3711#section-4.3.1.
    divs bytestrings'''
    s1,s2=   zero_pad(s1,s2)
    n_bytes= max(len(s1),len(s2))
    s1,s2=   bytes_to_int(s1), bytes_to_int(s2)
    tmp=     s1 % s2 if s2!=0 else 0
    return   int_to_bytes(tmp, n_bytes)


#------------- SRTP FUNCTIONS  ----------------
# python3
try: long
except: long = int

def aes_counter_encrypt( key, iv, data, decrypt=False):
    '''Basic AES en/decryption in counter mode'''
    assert type(iv) in (bytes,str,int,long)
    if type(iv)==str or type(iv) == bytes:
        iv = bytes_to_int(iv)
    counter= AESCounter.new( nbits=128, initial_value=iv)
    aes= AES.new(key=key, mode=AES.MODE_CTR, counter=counter )
    return aes.decrypt(data) if decrypt else aes.encrypt(data)

def srtp_packet_index( roc, seq, bytearray=False ):
    '''Calculates SRTP packet index given the Roll Over Counter and the
    RTP packet Sequence Number.
    https://tools.ietf.org/html/rfc3711#section-3.3.1'''
    result= roc*(2**16) + seq
    return result

def srtp_aes_counter_keystream( session_key, session_salt, packet_index, ssrc, keystream_size, counter_offset=0 ):
    '''Generates BYTE_SIZE bytes of keystream
    https://tools.ietf.org/html/rfc3711#section-4.1.1'''
    assert type(ssrc) in (int, long)
    assert type(packet_index) in (int, long)
    assert keystream_size <= 16 * 2**16 #128 bits per (AES) block, 2**16 blocks - this is the maximum RTP payload size
    assert keystream_size % 16 == 0 #keystream size  must be multiple of the AES block size
    assert len(session_salt)==112/8
    LOTS_OF_ZEROS= b'\0' * keystream_size
    ssrc=           int_to_bytes( ssrc, 4 )         #32 bits
    packet_index=   int_to_bytes( packet_index, 8)  #48 bits ROC + 16 bits SEQ
    counter_offset= int_to_bytes( counter_offset, 2 ) #this is for testing purposes only
    iv= xor(     session_salt+b'\0'*2,
                ssrc+b'\0'*8,
                packet_index+b'\0'*2,
                counter_offset ) #testing purposes only
    keystream= aes_counter_encrypt( session_key, iv, LOTS_OF_ZEROS )
    #print "keystream is", keystream.encode("hex")
    return keystream

def srtp_aes_counter_encrypt( session_key, session_salt, packet_index, ssrc, data, counter_offset=0 ):
    '''En/decrypts SRTP data using AES counter keystream.
    https://tools.ietf.org/html/rfc3711#section-4.1.1'''
    ds= len(data)
    keystream_size= ((ds//16)+1)*16 if (ds//16*16!=ds) else ds #nearest (upper-rounded) size to len(data) multiple of AES block size
    keystream= srtp_aes_counter_keystream( session_key, session_salt, packet_index, ssrc, keystream_size, counter_offset=0 )
    return xor(data, keystream[:ds])


def srtp_derive_key_aes_128( master_key, master_salt, rtcp=False):
    '''SRTP key derivation, https://tools.ietf.org/html/rfc3711#section-4.3'''
    assert len(master_key)==128/8
    assert len(master_salt)==112/8
    if rtcp:
        CIPHER_LABEL=      int_to_bytes( 3, 1 )
        AUTH_LABEL=        int_to_bytes( 4, 1 )
        SALT_LABEL=        int_to_bytes( 5, 1 )
    else:
        CIPHER_LABEL=      int_to_bytes( 0, 1 )
        AUTH_LABEL=        int_to_bytes( 1, 1 )
        SALT_LABEL=        int_to_bytes( 2, 1 )
    KEY_DERIVATION_RATE=   int_to_bytes( 0, 6 )
    PACKET_INDEX=          int_to_bytes( 0, 6 )
    LOTS_OF_ZEROS=         b'\0'*32                   #for PRNG

    index_div_kdr= srtp_div( PACKET_INDEX, KEY_DERIVATION_RATE )
    multiply_2_16=         lambda x: x+b'\0\0' #multiply by 2^16
    prng=                  partial( aes_counter_encrypt, key=master_key, data=LOTS_OF_ZEROS )
    derive_key_from_label= lambda label : prng(iv=multiply_2_16(xor(master_salt, label+index_div_kdr)))

    cipher_key= derive_key_from_label(CIPHER_LABEL)[:16] #128 bits
    salt_key=   derive_key_from_label(SALT_LABEL)[:14]   #112 bits
    auth_key=   derive_key_from_label(AUTH_LABEL)[:20]   #??? not sure of size

    return cipher_key, salt_key, auth_key

def srtp_verify_and_strip_signature( auth_key, rtp_packet, roc, hash_function=Crypto.Hash.SHA, hash_length=80 ):
    assert hash_length % 8 == 0
    hash_length = hash_length // 8

    h = HMAC( auth_key, rtp_packet[:-hash_length] + int_to_bytes(roc, 4), hash_function ).digest()
    if h[:hash_length] == rtp_packet[-hash_length:]:
        return rtp_packet[:-hash_length]
    else:
        raise AuthenticationFailure()

def srtcp_verify_and_strip_signature( auth_key, rtcp_packet, hash_function=Crypto.Hash.SHA, hash_length=80 ):
    assert hash_length % 8 == 0
    hash_length = hash_length // 8

    h = HMAC( auth_key, rtcp_packet[:-hash_length], hash_function ).digest()
    if h[:hash_length] == rtcp_packet[-hash_length:]:
        packet_i = bytes_to_int( rtcp_packet[-hash_length-4:-hash_length] )
        encrypted = packet_i & (1<<31) != 0
        packet_i = packet_i & ((1<<31) - 1)
        return rtcp_packet[:-hash_length-4], packet_i, encrypted
    else:
        raise AuthenticationFailure()

def srtp_sign_packet( auth_key, rtp_packet, roc, hash_function=Crypto.Hash.SHA, hash_length=80 ):
    assert(hash_length % 8 == 0)
    hash_length = hash_length // 8
    h = HMAC(auth_key, rtp_packet + int_to_bytes(roc, 4), hash_function ).digest()
    return rtp_packet + h[:hash_length]

def srtcp_sign_packet( auth_key, rtcp_packet, index, is_encrypted, hash_function=Crypto.Hash.SHA, hash_length=80 ):
    assert(hash_length % 8 == 0)
    hash_length = hash_length // 8
    index = index % (2**30)
    if is_encrypted:
        index += 1 << 31
    index = int_to_bytes(index, 4)
    h = HMAC(auth_key, rtcp_packet + index, hash_function ).digest()
    return rtcp_packet + index + h[:hash_length]


#------------- TEST FUNCTIONS ----------------

def test_srtp_key_derivation_vectors():
    #test srtp_derive_key_aes_128
    master_key=  a2b_hex('E1F97A0D3E018BE0D64FA32C06DE4139')
    master_salt= a2b_hex('0EC675AD498AFEEBB6960B3AABE6')
    ck,sk,ak= srtp_derive_key_aes_128(master_key, master_salt)
    assert ck==a2b_hex('C61E7A93744F39EE10734AFE3FF7A087')
    assert sk==a2b_hex('30CBBC08863D8C85D49DB34A9AE1')
    assert ak.startswith(a2b_hex('CEBE321F6FF7716B6FD4AB49AF256A15')) # not sure of size

def test_srtp_aes_ctr_vectors():
    LOTS_OF_ZEROS= b'\0' * 16 * 2**16
    session_key= a2b_hex('2B7E151628AED2A6ABF7158809CF4F3C')
    session_salt= a2b_hex('F0F1F2F3F4F5F6F7F8F9FAFBFCFD')
    roc= 0
    seq= 0
    ssrc=0
    packet_i= srtp_packet_index(roc, seq)
    result= srtp_aes_counter_encrypt( session_key, session_salt, packet_i, ssrc, LOTS_OF_ZEROS)
    assert result[0x0000*16:0x0001*16]==a2b_hex('E03EAD0935C95E80E166B16DD92B4EB4')
    assert result[0x0001*16:0x0002*16]==a2b_hex('D23513162B02D0F72A43A2FE4A5F97AB')
    assert result[0x0002*16:0x0003*16]==a2b_hex('41E95B3BB0A2E8DD477901E4FCA894C0')
    assert result[0xfeff*16:0xff00*16]==a2b_hex('EC8CDF7398607CB0F2D21675EA9EA1E4')
    assert result[0xff00*16:0xff01*16]==a2b_hex('362B7C3C6773516318A077D7FC5073AE')
    assert result[0xff01*16:0xff02*16]==a2b_hex('6A2CC3787889374FBEB4C81B17BA6C44')

def test_srtp_packet_index_respected():
    session_key = a2b_hex('66e94bd4ef8a2c3b884cfa59ca342b2e')
    session_salt = a2b_hex('b5b03421de8bbffc4eadec767339')
    roc = 0
    data = b'hello\n\0'
    ssrc = 0xdeadbeef

    seq = 1
    packet_i= srtp_packet_index(roc, seq)
    ks = srtp_aes_counter_keystream(session_key, session_salt, packet_i, ssrc, 16)
    result = srtp_aes_counter_encrypt( session_key, session_salt, packet_i, ssrc, data)
    assert ks == a2b_hex('5a11957692c23f3f7ee8ddc76c38df14')
    assert result == a2b_hex('3274f91afdc83f')

    seq += 1
    packet_i= srtp_packet_index(roc, seq)
    ks = srtp_aes_counter_keystream(session_key, session_salt, packet_i, ssrc, 16)
    result = srtp_aes_counter_encrypt( session_key, session_salt, packet_i, ssrc, data)
    assert ks == a2b_hex('20afa8428e8c4fd4699156c650047339')
    assert result == a2b_hex('48cac42ee1864f')

    seq += 1
    packet_i= srtp_packet_index(roc, seq)
    ks = srtp_aes_counter_keystream(session_key, session_salt, packet_i, ssrc, 16)
    result = srtp_aes_counter_encrypt( session_key, session_salt, packet_i, ssrc, data)
    assert ks == a2b_hex('41c32fab452ca5d13a536a93ece44f7d')
    assert result == a2b_hex('29a643c72a26a5')

def test_xor():
    assert xor(b'\0\0\1', b'\0\0\2') == b'\0\0\3'
    assert xor(b'\0\0\1', b'\0\0\2', b'\1\0\0') == b'\1\0\3'
    assert xor(b'\0\0\1', b'\0\0\2', b'\1\1\0\0') == b'\1\1\0\3'
    # four argument version used in srtp_aes_counter_keystream
    assert xor(b'\0\0\1', b'\0\0\2', b'\1\0\0', b'\0\1\0') == b'\1\1\3'

def test_srtp_auth():
    m = b"hello_rtp"
    master_key=  a2b_hex('00000000000000000000000000000000')
    master_salt= a2b_hex('0000000000000000000000000000')
    ck,sk,ak= srtp_derive_key_aes_128(master_key, master_salt)
    assert b2a_hex(ak) == b'788bcd111ecf73d4e78d2e21bef55460daacdaf7'

    ma = srtp_sign_packet(ak, m, 0)

    assert b2a_hex(ma[-10:]) == b'e60c68053178ee795142'
    assert srtp_verify_and_strip_signature(ak, ma, 0) == m
    try:
        srtp_verify_and_strip_signature(ak, ma, 1) # wrong roc should fail authentication
        assert False
    except AuthenticationFailure:
        pass

    try:
        srtp_verify_and_strip_signature(ak, b'\xff' + ma[1:], 1) # modified message should fail auth
        assert False
    except AuthenticationFailure:
        pass

    ck,sk,ak= srtp_derive_key_aes_128(master_key, master_salt, rtcp=True)
    encrypted_srtcp = True
    packet_i_srtcp = 1
    data = a2b_hex ('80cc000810feff99466c75782105000310feff990000100200001603000000090000000400000001a0573cb69ef3c96e1253')
    data2 = a2b_hex('80cc000810feff99466c75782105000310feff990000100200001603000000090000000480000002e24513e079e366eb82e6')

    assert srtcp_sign_packet(ak, data[:-14], packet_i_srtcp, not encrypted_srtcp) == data
    assert srtcp_verify_and_strip_signature(ak, data) == (data[:-14], packet_i_srtcp, not encrypted_srtcp)

    assert srtcp_sign_packet(ak, data[:-14], packet_i_srtcp+1, encrypted_srtcp) == data2
    assert srtcp_verify_and_strip_signature(ak, data2) == (data2[:-14], packet_i_srtcp+1, encrypted_srtcp)

def run_tests():
    test_xor()
    test_srtp_key_derivation_vectors()
    test_srtp_aes_ctr_vectors()
    test_srtp_packet_index_respected()
    test_srtp_auth()

if __name__=='__main__':
    run_tests()
