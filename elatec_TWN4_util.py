#Elatec Card Writer - Python program that uses the Simple Protocol for Elatec TWN4
#Version 1.0

#MIT License

#Copyright (c) 2026 Jonathan Campbell

#Permission is hereby granted, free of charge, to any person obtaining a copy
#of this software and associated documentation files (the "Software"), to deal
#in the Software without restriction, including without limitation the rights
#to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
#copies of the Software, and to permit persons to whom the Software is
#furnished to do so, subject to the following conditions:

#The above copyright notice and this permission notice shall be included in all
#copies or substantial portions of the Software.

#THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
#IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
#FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
#AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
#LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
#OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
#SOFTWARE.

#using PyCryptodome 'pip install pycryptodome'
#using ecdsa 'pip install ecdsa'
import sys
import platform
import serial
import serial.tools.list_ports
import time
import datetime
import re
import secrets

from Crypto.Cipher import AES
from Crypto.Util.Padding import pad, unpad
from Crypto import Random

from ecdsa import VerifyingKey, NIST256p
from ecdsa.util import sigdecode_string
import hashlib

#Data Type                  |Description
#[Byte]:                        One single byte (sent as two hex digits)
#[UInt16]:                      Two bytes (LSB first)
#[UInt32]:                      Four bytes (LSB first)
#[Bool]:                        One single byte which can hold two values: 0 or 1
#[Byte Array(n)]:               A sequence of bytes with known and fixed number of bytes. The number of
#                                   bytes is not transferred explicitely, because both host and TWN4 do
#                                   know this number.
#[Byte Array(Var)]:             A sequence of bytes, where the first byte holds the number of following bytes
#[Byte Array(Var), x LB]:       A sequence of bytes, where the first x bytes hold the number of following bytes
#[ASCII string]:                A sequence of bytes which contain ASCII characters, except the first byte
#                                   which holds the number of following bytes

#Define True and False for TWN4 response
ByteTrue  = b'\x00\x01'
ByteFalse = b'\x00\x00'

#MIFARE CardTypes
MIFAREMini              = 3
MIFAREClassic1K         = 1
MIFAREClassic2K         = 2
MIFAREClassic4K         = 4
MIFAREPlus2KSL2         = 522
MIFAREPlus4KSL2         = 542
RFU                     = 99
SmartMXMIFAREClassic4K  = 84
SmartMXMIFAREClassic1K  = 81
MIFAREDESFire           = 6
MIFAREDUOX              = 7
MIFARETagNPlay          = 98
MIFAREOther             = 666


#LED Definitions
REDLED    = b'\x01'
GREENLED  = b'\x02'
YELLOWLED = b'\x04'
ALLLED    = b'\x07' #OR of REDLED, GREENLED, and YELLOWLED

# Define RF Tag Types
lftagtype = {}
lftagtype['NOTAG'] = 0
#LF Tags
lftagtype['LFTAG_EM4102']    = 0x40 # "EM4x02/CASI-RUSCO" (aka IDRO_A)
lftagtype['LFTAG_HITAG1S']   = 0x41 # "HITAG 1/HITAG S"   (aka IDRW_B)
lftagtype['LFTAG_HITAG2']    = 0x42 # "HITAG 2"           (aka IDRW_C)
lftagtype['LFTAG_EM4150']    = 0x43 # "EM4x50"            (aka IDRW_D)
lftagtype['LFTAG_AT5555']    = 0x44 # "T55x7"             (aka IDRW_E)
lftagtype['LFTAG_ISOFDX']    = 0x45 # "ISO FDX-B"         (aka IDRO_G)
lftagtype['LFTAG_EM4026']    = 0x46 # N/A                 (aka IDRO_H)
lftagtype['LFTAG_HITAGU']    = 0x47 # N/A                 (aka IDRW_I)
lftagtype['LFTAG_EM4305']    = 0x48 # "EM4305"            (aka IDRW_K)
lftagtype['LFTAG_HIDPROX']   = 0x49	# "HID Prox"
lftagtype['LFTAG_TIRIS']     = 0x4A	# "ISO HDX/TIRIS"
lftagtype['LFTAG_COTAG']     = 0x4B	# "Cotag"
lftagtype['LFTAG_IOPROX']    = 0x4C	# "ioProx"
lftagtype['LFTAG_INDITAG']   = 0x4D	# "Indala"
lftagtype['LFTAG_HONEYTAG']  = 0x4E	# "NexWatch"
lftagtype['LFTAG_AWID']      = 0x4F	# "AWID"
lftagtype['LFTAG_GPROX']     = 0x50	# "G-Prox"
lftagtype['LFTAG_PYRAMID']   = 0x51	# "Pyramid"
lftagtype['LFTAG_KERI']      = 0x52	# "Keri"
lftagtype['LFTAG_DEISTER']   = 0x53	# "Deister"5
lftagtype['LFTAG_CARDAX']    = 0x54	# "Cardax"
lftagtype['LFTAG_NEDAP']     = 0x55	# "Nedap"
lftagtype['LFTAG_PAC']	     = 0x56	# "PAC"
lftagtype['LFTAG_IDTECK']    = 0x57	# "IDTECK"
lftagtype['LFTAG_ULTRAPROX'] = 0x58	# "UltraProx"
lftagtype['LFTAG_ICT']	     = 0x59	# "ICT"
lftagtype['LFTAG_ISONAS']    = 0x5A	# "Isonas"
# HF Tags
hftagtype = {}
hftagtype['NOTAG'] = 0
hftagtype['HFTAG_MIFARE']    = 0x80	# "ISO14443A/MIFARE"
hftagtype['HFTAG_ISO14443B'] = 0x81	# "ISO14443B"
hftagtype['HFTAG_ISO15693']  = 0x82	# "ISO15693"
hftagtype['HFTAG_LEGIC']     = 0x83	# "LEGIC"
hftagtype['HFTAG_HIDICLASS'] = 0x84	# "HID iCLASS"
hftagtype['HFTAG_FELICA']    = 0x85	# "FeliCa"
hftagtype['HFTAG_SRX']       = 0x86	# "SRX"
hftagtype['HFTAG_NFCP2P']    = 0x87	# "NFC Peer-to-Peer"
hftagtype['HFTAG_BLE']       = 0x88	# "Bluetooth Low Energy"
hftagtype['HFTAG_TOPAZ']     = 0x89  # "Topaz"
hftagtype['HFTAG_CTS']       = 0x8A  # "CTS256 / CTS512"
hftagtype['HFTAG_BLELC']     = 0x8B	# "Bluetooth Low Energy LEGIC Connect"

lftagtype['ALL_LFTAGS']      = 0xFFFFFFFF
hftagtype['ALL_HFTAGS']      = 0xFFFFFFFF

TAGMASK         = 0x1F

TAG_TYPES_LF = {k: lftagtype[k] for k in ['NOTAG'] if k in lftagtype}
TAG_TYPES_HF = {k: hftagtype[k] for k in ['HFTAG_MIFARE'] if k in hftagtype}

DEVTYPE = {}
DEVTYPE["TWN4 LEGIC"]       = 10
DEVTYPE["TWN4 MIFARE"]      = 11
DEVTYPE["TWN4 LEGIC 63"]    = 12

CRYTPO_ENV0  = "00"
CRYTPO_ENV1  = "01"
CRYTPO_ENV2  = "02"
CRYTPO_ENV3  = "03"
DESF_KEYTYPE_AES         = "02"
DESF_AUTHMODE_COMPATIBLE = "00"
DESF_AUTHMODE_EV1        = "01"
DESF_AUTHMODE_EV2        = "02"

# Define the serial commands
GET_VERSION_STRING          = "0004FF\r"
GET_DEVICE_UID              = "0008\r"
GET_DEVICE_TYPE             = "0006\r"
BEEP                        = "0407%s%s%s%s\r"          #[0407][Byte: Volume][UInt16: Frequency][UInt16: OnTime][UInt16: OffTime]
SHORT_BEEP                  = "0407506009F401F401\r"    #volume: 50, Freq: 6009, OnTime: F401, OffTime: F401
SET_TAG_TYPES               = "0502%s%s\r"              #[0502][UInt32: TagTypesLF][UInt32: TagTypesHF]
SEARCH_TAG                  = "050020\r"                #[0500][Byte: MaxIDBytes]
SELECT_TAG                  = "1209%s%s\r"              #[1209][Byte Array Size][Byte Array(Var): UID]
LEDINIT                     = "0410%s\r"                #[0410][Byte: LEDs] -bitwise or of LED Definitions
LEDON                       = "0411%s\r"                #[0411][Byte: LEDs]
LEDOFF                      = "0412%s\r"                #[0411][Byte: LEDs]
GET_SAK                     = "1205\r"                  #[1205]
GET_ATS                     = "120020\r"                #[1200][Byte; MaxATSByteCnt] - here we use 32 bytes
LOGIN_SECTOR                = "0B00%s%s%s\r"            #[0B00][Byte Array(6): Key][Byte: KeyType][Byte: Sector]
READ_BLOCK                  = "0B01%s\r"                #[0B01][Byte: Block]
WRITE_BLOCK                 = "0B02%s%s\r"              #[0B02][Byte: Block][Byte Array(16): Data]
DESFire_SelectApplication   = "0F03%s%s00\r"            #[0F03][Byte: CryptoEnv][UInt32: AID]
DESFire_Authenticate        = "0F04%s%s%s%s%s%s\r"      #[0F04][Byte: CryptoEnv][Byte: KeyNoTag][Byte Array(Var): Key][Byte: KeyType][Byte: Mode]
DESFire_ReadData            = "0F08%s%s%s%s%s\r"        #[0F07][Byte: CryptoEnv][Byte: FileNo][UInt16: Offset][Byte: Length][Byte: CommSet]
NXP_GETVERSION4             = "1203016020\r"            #NXP Layer4 GetVersion Command

#PKOC Commands
PKOC_SELECT                 = "12030E00A4040008A000000898000001000A\r" #14443_4_TDX[1203][Byte Array(Var): TX][Byte: MaxRXByteCnt]
                                                                       #PKOC Select 
                                                                       # CLA  00  Default class
                                                                       # INS  A4  Select
                                                                       #  P1  04  Select by DF Name (AID)
                                                                       #  P2  00  First or only occurence
                                                                       #  Lc  08  Data Length
                                                                       #Data  A000000898000001    AID
                                                                       #  Le  00  Maximum length of expected response data
                                                                       
PKOC_AUTHENTICATE           = "1203%s8080000138%s008A\r" #14443_4_TDX[1203][Byte Array(Var): TX][Byte: MaxRXByteCnt]
                                                         #PKOC Authenticate
                                                         # CLA  80  Manufacturer specific class
                                                         # INS  80  Authentication
                                                         #  P1  00  shall be set to 0
                                                         #  P2  01  shall be set to 1
                                                         #  Lc  38  Data Length
                                                         #Data  Var Protocol Version, Transaction ID, Reader Identifier
                                                         #  Le  00  Maximum length of expected response data
#Global variables
DEVICEUID     = b'\x00'
VERSIONSTRING = bytes()
DEVICETYPE    = None

#Helper Functions
def is_hex(s, l=255):
    # Regex: Matches optional 0x/0X prefix followed by valid hex characters.
    return bool(re.match(r"^[0-9a-fA-F]+$", s) and len(s) <= l)

def hexlify(data):
    return ' '.join(f'{c:0>2X}' for c in data)

def hexlify_string(text):
    if text != None:
        return ' '.join(text[i : i + 2] for i in range(0, len(text)-1, 2))
    else:
        return None

def select_keys_menu(input_dict):
    keys = list(input_dict.keys())
    selected_indices = set()

    while True:
        print("\n--- Select Keys (Toggle options by entering the number) ---")
        for i, key in enumerate(keys):
            # Show a checkmark next to selected keys
            status = "[X]" if i in selected_indices else "[ ]"
            print(f"{i + 1}. {status} {key}")
        
        print("Type 'd' when you are done.")
        choice = input("Enter a number or 'd': ").strip().lower()

        if choice == 'd':
            break
        
        if choice.isdigit():
            idx = int(choice) - 1
            if 0 <= idx < len(keys):
                # Toggle selection status
                if idx in selected_indices:
                    selected_indices.remove(idx)
                else:
                    selected_indices.add(idx)
            else:
                print("Invalid number. Please try again.")
        else:
            print("Invalid input. Please enter a valid number or 'd'.")

    # Filter original dictionary using a dictionary comprehension
    chosen_keys = [keys[idx] for idx in selected_indices]
    return {k: input_dict[k] for k in chosen_keys if k in input_dict}

def string_to_bytes(s):
    hexarray = bytearray()
    for byte in range(0, len(s), 2):
        chunk = int(s[byte:byte+2],16)
        hexarray.append(chunk)
    return hexarray

def left_shift_one_bit(data: bytes) -> tuple[bytearray, bool]:
    num_bytes = len(data)
    # Convert array to a big int
    val = int.from_bytes(data, byteorder='big')
    
    # Shift left
    shifted_val = val << 1
    
    # Detect overflow based on expected bit width
    max_bits = num_bytes * 8
    overflow = shifted_val >= (1 << max_bits)
    
    # Mask to keep the correct byte length and convert back
    masked_val = shifted_val & ((1 << max_bits) - 1)
    return bytearray(masked_val.to_bytes(num_bytes, byteorder='big')), overflow

#Helper functions for Elatec capabilities

def set_tagtype(tagtype):
    tagbyte = 0
    #check for ALL_TAGS or NOTAG as we will not use the TAGMASK
    if "ALL_LFTAGS" in tagtype or "ALL_HFTAGS" in tagtype:
        tagbyte = 0xFFFFFFFF
    elif "NOTAG" in tagtype:
        tagbyte = 0
    else:
        #iterate through the dictionary and use the taskmask to build the tagtype command string
        for typehex in tagtype.values():
            tagtypemask = 1 << (typehex & TAGMASK)
            #print(f"tagtypemask = {tagtypemask}")
            tagbyte |= tagtypemask
            #print(f"tagbyte = {tagbyte}")
    #convert the end result to a bytearray in little endian order as required by the TWN4
    tagtypebyte = tagbyte.to_bytes(4, byteorder='little')
    #return the bytearray as a hexstring
    return tagtypebyte.hex()

def set_classic_sectorkey(sector, sector_key, key_type):
    while True:
        sector = input("\n\nEnter the sector number in hex (00 to 0F): ").upper().strip()
        if is_hex(sector, 2):
            break
    while True:
        sector_x_key = input("Enter the sector key (6 bytes): ").strip().upper()
        if is_hex(sector_key, 12):
            break
    while True:
        key_type = input("Enter the key type (A or B): ").strip().upper()
        if key_type == "A":
            key_type = "00"
            break
        elif key_type == "B":
            key_type = "01"
            break
    return

def set_classic_newkey():
    while True:
        new_sector_key = input("\n\nEnter the new sector key (16 bytes) or None: ").strip().upper()
        if new_sector_key == "None":
            new_sector_key = None
            break
        elif is_hex(new_sector_key, 32):
            break
    return new_sector_key

def set_classic_writedata():
    data_to_write  = {1 : "00000000000000000000000000000000", 2: "00000000000000000000000000000000", 3: "00000000000000000000000000000000"}
    while True:
        data_to_write[1] = input("\n\nEnter the data to write block 1 (16 bytes): ").strip().upper()
        if is_hex(data_to_write[1], 32):
            while True:
                data_to_write[2] = input("Enter the data to write block 2 (16 bytes): ").strip().upper()
                if is_hex(data_to_write[2], 32):
                    while True:
                        data_to_write[3] = input("Enter the data to write block 3 (16 bytes): ").strip().upper()
                        if is_hex(data_to_write[3], 32):
                            break
                    break
            break
    return data_to_write

#TWN4 Functions
def send_command(ser, command, *args, timeout=2):
    #response = bytearray()
    hexarray = bytearray()
    formatted_command = command % args
    try:
        #print(f"formatted command: {formatted_command}")
        #print(f"formatted command ascii: {formatted_command.encode("ascii")}")
        #Write the bytes *data* to the port. This should be of type ``bytes`` 
        #(or compatible such as ``bytearray`` or ``memoryview``). Unicode
        #strings must be encoded (e.g. ``'hello'.encode('utf-8')``.
        bytes_written = ser.write(formatted_command.encode("ascii"))

        #wait for out queue to clear
        end_time = time.time() + timeout
        while ser.out_waiting > 0:
            if time.time() > end_time:
                print("Error: timeout occurred while waiting for sending command.")
                return -1
        #did we send all the bytes of the command
        if not bytes_written == len(formatted_command):
            print("Error: command not fully sent")
            return -1

        #wait for inbound queue to fill, this is better than blocking on ser.read()
        end_time = time.time() + timeout
        while ser.in_waiting == 0:
            if time.time() > end_time:
                print("Error: timeout occurred while waiting for inbound queue.")
                return -1
        
        #read the inbound queue till it empties or we read \r
        end_time = time.time() + timeout    
        while ser.in_waiting > 0:
            if time.time() > end_time:
                print("Error: timeout occurred while waiting for response.")
            response = ser.read_until(expected=b'\r').strip()
            #print(f"serial response: {response}")
            #break
            #byte = ser.read(2)
            #if byte == b'\r':
            #    break
            #response.append(int(byte, 16))

        #convert the response to hexadecimal bytes array
        hexarray = string_to_bytes(response)
        #for byte in range(0, len(response), 2):
        #    chunk = int(response[byte:byte+2],16)
        #    hexarray.append(chunk)

    except serial.SerialException as e:
        print(f"Serial exception: {e}")
        return -1
    except ValueError as e:
        print(f"Serial Value Error: {e} ")
        return -1
    return hexarray

def mifare_type(ser):
    #reset found card type
    MIFAREType = None
    #follow NXP AN10833 documentation for determining card type
    sak = send_command(ser, GET_SAK)
    #check if GetSAK succeeded
    if sak[0:2] == ByteTrue:
        #convert SAK return to binary string so we can check bits 
        binstr = bin(sak[2])[2:].zfill(8)      
        if binstr[6] == '0': #check if byte 2 = 1, if yes RFU
            if binstr[4] == '1': #b4 = 1
                if binstr[3] == '0': #b5 = 0
                    if binstr[7] == '0': #b1 = 0
                        if binstr[2] == '0': #b6 = 0
                            ats = send_command(ser, GET_ATS)
                            if ats[0:2] == ByteFalse:
                                if sak[2] == 8:
                                    MIFAREType = MIFAREClassic1K
                                    print("MIFARE Classic 1K found")
                        else: #b6 = 1
                            if sak[2] == 28:
                                MIFAREType = SmartMXMIFAREClassic1K
                                print("SmartMX with MIFARE Classic 1K found")
                    else: #b1 = 1
                        if sak[2] == 9:
                            MIFAREType = MIFAREMini
                            print("MIFARE Mini found")
                else: #b5 = 1
                    if binstr[7] == '1': #b1=1
                        if sak[2] == 19:
                            MIFAREType = MIFAREClassic2K
                    else:
                        if binstr[2] == '0': #b6=0
                            ats = send_command(ser, GET_ATS)
                            if ats[0:2] == ByteFalse:
                                if sak[2] == 18:
                                    MIFAREType = MIFAREClassic4K
                                    print("MIFARE Classic 4K found")
                        else:
                            if sak[2] == 38:
                                MIFAREType = SmartMXMIFAREClassic4K
                                print("SmartMX with MIFARE Classic 4K found")
            else: #b4 = 0
                if binstr[3] == '1': #b5=1
                    if binstr[7] == '1': #b1=1
                        if sak[2] == 11: 
                            MIFAREType = MIFAREPlus4KSL2
                            print("MIFARE Plus 4K in SL2 found")
                    else:
                        if sak[2] == 10:
                            MIFAREType = MIFAREPlus2KSL2
                            print("MIFARE Plus 2K in SL2 found")
                else:
                    if binstr[7] == '0': #b1=0
                        if binstr[2] == '1': #b6=1, we change to ATS and enter 14443-4 layer
                            ats = send_command(ser, GET_ATS)
                            if ats[0:2] == ByteTrue:
                                version = send_command(ser, NXP_GETVERSION4)
                                print(f"ATS Version: {hexlify(version)}")
                                if len(version) < 16:
                                    MIFAREType = MIFAREOther
                                    print("Non MIFARE type found")
                                elif version[6] == 0x01 and version[9] == 0xA0: #duox is HW Type 0x01 and HW Major Ver 0xAD (bytes 2 and 5 plus 1 for prefix) 
                                    MIFAREType = MIFAREDUOX
                                    print("MIFARE DUOX found")
                                elif version[6] == 0x01 or version[6] == 0x81: #HW Type 0x01 or 0x81 = DESFire
                                        MIFAREType = MIFAREDESFire
                                        print("MIFARE DESFire found")
                            else: #MIFARE Plus
                                pass
                    else:
                        MIFAREType = MIFARETagNPlay
                        print("TagnPlay found")
        else:
            MIFAREType = RFU
    else:
        print("Error getting card type")
    return MIFAREType

def init_reader(ser, lftag, hftag):
    global DEVICEUID
    global VERSIONSTRING
    global DEVICETYPE
    print("\n\n===================================")
    response = send_command(ser, GET_DEVICE_UID)
    #first byte of return will be x00 if successful
    if response[0:1] == b'\x00':
        DEVICEUID = response[1:13] #Only returns 13 bytes, with last 12 being the UID
        print(f"Device UID: {hexlify(DEVICEUID)}")
    else:
        print(f"Failed to get reader device UID, response was {response}")
    response = send_command(ser, GET_DEVICE_TYPE)
    #first byte of return will be x00 if successful
    if response[0:1] == b'\x00':
        DEVICETYPE = response[1:2] #second byte is Device Type
        print(f"Device Type: {next(k for k, v in DEVTYPE.items() if v == int.from_bytes(DEVICETYPE, byteorder='big'))}")
    else:
        print(f"Failed to get reader device type, response was {response}")
    response = send_command(ser, GET_VERSION_STRING)
    #first byte of return will be x00 if successful
    if response[0:1] != b'\x00':
        print ("Failed to get reader version string")
    else:
        VERSIONSTRING = response[1:len(response)+1]
        print(f"Version string: {VERSIONSTRING.decode('ascii')}")
    lf = set_tagtype(lftag)
    hf = set_tagtype(hftag)
    print(f"Set card type to {lf + hf}")
    response = send_command(ser, SET_TAG_TYPES % (lf, hf))
    if response != b'\x00':
        print(f"Failed to set scan tag types and initialize reader {response}")
        return False
    #led1 = bytes(REDLED | GREENLED for REDLED, GREENLED in zip(REDLED, GREENLED))
    #leds = bytes(led1 | YELLOWLED for led1, YELLOWLED in zip(led1, YELLOWLED))
    #print(f"all leds {leds.hex()}")
    response = send_command(ser, LEDINIT % ALLLED.hex()) #LEDInit
    if response == b'\x00':
        response = send_command(ser, LEDON % bytes(REDLED | GREENLED for REDLED, GREENLED in zip(REDLED, GREENLED)).hex()) #LEDOn (RED|GREEN)
        if response != b'\x00':
            print("Failed to initalize LEDs")    
    else:
        print("Failed to initalize LEDs")    
    response = send_command(ser, LEDOFF % REDLED.hex()) #LEDOff (RED)
    print("LEDs initialized")
    response = send_command(ser, SHORT_BEEP)
    if response == b'\x00':
        print("Reader is ready")
    else:
        print(f"Failed to sound \'beep\'")
    return True

def read_uid(ser):
    uid = b'\x00\x00'
    mifaretype = None
    input("\nPress key when ready to search for card")
    #print(f"Search operation started at {datetime.datetime.now()}")
    print(f"Sending command: {SEARCH_TAG}")
    scan_response = send_command(ser, SEARCH_TAG)
    #print(f"scan_response: {scan_response}")
    if scan_response == b'\x00\x00':
        print("No card found")
    else:
        uid = scan_response[5:len(scan_response)]
        print(f"\nUID: {hexlify(uid)}")
        mifaretype = mifare_type(ser)
    #print(f"Search operation stopped at {datetime.datetime.now()}")
    return uid, mifaretype

def sendtocard(ser):    
    uid = read_uid(ser)
    #send command loop as long as we found a card
    while uid != b'\x00\x00':
        command = input("\nEnter the hex command with no prefix [0x] or \'exit\' ") + '\r'
        if command == "exit\r":
            break
        #validate if we have a hex string
        if is_hex(command.strip(), 255):
            #make sure there is no 0x prefix
            print(f"Sending command: {command}")
            command_response = send_command(ser, command)
            if command_response == -1:
                print("Command failed")
            else:
                print(f"Command response: {hexlify(command_response)}")
    return

def login_mifare_classic(ser, sector, sector_key, key_type):
    # Step 1: Login to the sector
    uid, mifaretype = read_uid(ser)
    if mifaretype == MIFAREClassic1K:
        #read loop as long as we found a card
        if uid != ByteFalse:
            response = send_command(ser, SELECT_TAG % (format(len(uid), '02X'), uid.hex().upper()))
            if response == ByteTrue: #found card and selected
                response = send_command(ser, LOGIN_SECTOR % (sector_key, key_type, sector))
                if response == ByteTrue:
                    send_command(ser, SHORT_BEEP)
                    print("Logged into card")
                else:
                    print(f"Error: unable to login to sector {sector} with key {sector_key}")
                    return False
            else:
                print(f"Error: found card {hexlify(uid)} but unable to select")
                return False
    else:
        print("Not a MiFare Classic 1K card")
        return False
    return True

def read_mifare_classic_block(ser, sector, sector_key, key_type):
    block0     = b'\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'
    block1     = b'\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'
    block2     = b'\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'
    if login_mifare_classic(ser, sector, sector_key, key_type) != True:
        response = send_command(ser, READ_BLOCK % (hex(int(sector)*4))[2:]) #read block 0
        if response[0:2] == ByteTrue:
            block0 = response[2:len(response)]
            print(f"Block 0: {hexlify(block0)}")
            response = send_command(ser, READ_BLOCK % (hex((int(sector)*4)+1))[2:]) #read block 1
            if response[0:2] == ByteTrue:
                block1 = response[2:len(response)]
                print(f"Block 1: {hexlify(block1)}")
                response = send_command(ser, READ_BLOCK % (hex((int(sector)*4)+2))[2:]) #read block 2, block 3 is trailing data so skip
                if response[0:2] == ByteTrue:
                    block2 = response[2:len(response)]
                    print(f"Block 2: {hexlify(block2)}")
                else:
                    print(f"Failed to read Block 2. Response: {response}")
            else:
                print(f"Failed to read Block 1. Response: {response}")
        else:
            print(f"Failed to read Block 0. Response: {response}")
    return block0, block1, block2

def write_new_mifare_sector_key(ser, sector, sector_key, key_type, new_sector_key):
    if new_sector_key != None:
        key_block = (hex((int(sector)*4)+3))[2:]

        print(f"Sector set to: {sector}")
        print(f"Sector key set to: {hexlify_string(sector_key)}")
        print(f"Key type set to: {key_type}")
        print(f"Key block set to: {key_block}")
        print(f"New key to write: {new_sector_key}")

        # Step 1: Login to the sector
        if login_mifare_classic(ser, sector, sector_key, key_type) != True:
            return False

        # Step 2: Write the new sector key
        #print(f"Write operation started at {datetime.datetime.now()}")

        print(f"Keyblock is = {key_block}")
        print("Writing new sector key")
        print(f"Write key command: {WRITE_BLOCK % (key_block, new_sector_key)}")
        response = send_command(ser, WRITE_BLOCK % (key_block, new_sector_key))
        if response != ByteTrue:
                print(f"Failed to write new sector key to sector {sector} with response {response}.")
                return False
        print("Wrote new sector key")

    return True

def write_client_data_to_mifare_classic(ser, sector, sector_key, key_type, data_to_write):
    #sector_number = int(sector, 16)
    #starting_write_block = format(int(sector, 16) * 4, '02X')
    #key_block = format(sector_number * 4 + 3, '02X')
    block = int(sector)*4

    print(f"Sector set to: {sector}")
    print(f"Sector key set to: {hexlify_string(sector_key)}")
    print(f"Key type set to: {key_type}")
    print(f"Block 1, 2 and 3 set to: {hex(block)[2:]}, {hex(block+1)[2:]}, {hex(block+2)[2:]}")
    print(f"Block 1 data to write: {hexlify_string(data_to_write[1])}")
    print(f"Block 2 data to write: {hexlify_string(data_to_write[2])}")
    print(f"Block 3 data to write: {hexlify_string(data_to_write[3])}")

    # Step 1: Login to the sector
    if login_mifare_classic(ser, sector, sector_key, key_type) != True:
        return False
    
    # Step 2: Write the data to the starting block and subsequent blocks if necessary
    response = send_command(ser, WRITE_BLOCK % (hex(block)[2:], data_to_write[1])) #write block 0
    if response == ByteTrue:
        response = send_command(ser, WRITE_BLOCK % (hex(block+1)[2:], data_to_write[2])) #write block 1
        if response == ByteTrue:
            response = send_command(ser, WRITE_BLOCK % (hex(block+2)[2:], data_to_write[3])) #write block 2
            if response == ByteTrue:
                print("Data written successfully to Blocks 1, 2 and 3")
            else:
                print("Block 3 write failed")
                return False
        else:
            print("Block 2 write failed")
            return False
    else:
        print("Block 1 write failed")
        return False
    return True

def read_desfire_data(ser, readkey, aid, filenum, cryptoenv):
    uid, mifaretype = read_uid(ser)
    if mifaretype == MIFAREDESFire:
        #read loop as long as we found a card
        if uid != ByteFalse:
            #select card
            response = send_command(ser, SELECT_TAG % (format(len(uid), '02X'), uid.hex().upper()))
            if response == ByteTrue: #found card and selected
                #we use all zeroes for AES CBC IV
                iv = b'\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'                
                M =  bytearray([ 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 ]);
                #convert readkey to bytes
                keyarray = string_to_bytes(readkey)
                print(f"Read key = {hexlify(keyarray)}")
                #convert aid to bytes
                aidarray = string_to_bytes(aid)

                #derive the diversified key
                cipher = AES.new(keyarray, AES.MODE_CBC, iv=iv)
                k0 = cipher.encrypt(iv)
                print(f"k0 = {hexlify(k0)}")
                k1, overflow = left_shift_one_bit(k0)
                if overflow:
                    k1[15] ^= 0x87
                print(f"k1 = {hexlify(k1)}")
                k2, overflow = left_shift_one_bit(k1)
                if overflow:
                    k2[15] ^= 0x87
                print(f"k2 = {hexlify(k2)}")
                for byte in range(1, 8, 1):
                    M[byte] = uid[byte-1]
                print(f"M  = {hexlify(M)}")
                for byte in range(16, 32, 1):
                    M[byte] = k2[byte-16]
                print(f"D  = {hexlify(M)}")
                cipher = AES.new(keyarray, AES.MODE_CBC, iv=iv)
                D = cipher.encrypt(M)
                print(f"Encrypted D = {hexlify(D)}")
                divkey = bytearray()
                for byte in range(16, 32, 1):
                    divkey.append(D[byte])
                print(f"Diversified Key = {hexlify(divkey)}")

                #we submit the Application ID in reverse byte order
                revaid = bytearray()
                revaid.append(aidarray[2])
                revaid.append(aidarray[1])
                revaid.append(aidarray[0])
                #print(f"reverse aid: {revaid.hex().upper()}")

                #select application and authenticate with diversified key
                response = send_command(ser, DESFire_SelectApplication % (cryptoenv, revaid.hex().upper()))
                if type(response) == bytearray and response[0:2] == ByteTrue:
                    print(f"AID {aid} selected")
                    response = send_command(ser, DESFire_Authenticate % (cryptoenv, "01", "10", divkey.hex().upper(), DESF_KEYTYPE_AES, DESF_AUTHMODE_EV2))
                    print(f"response: {response}")
                    if type(response) == bytearray and response[0:2] == ByteTrue:
                        print("DESFire Autenthication successful")
                        data = send_command(ser, DESFire_ReadData % (cryptoenv, filenum, "0000", "30", "03"))
                        if type(data) == bytearray and data[0:2] == ByteTrue:
                            return data[2:len(data)]
                        else:
                            print(f"Failed to read data for file {filenum}")
                    else:
                        print(f"Failed to authenticate to AID {hexlify_string(aid)}")
                else:
                    print(f"Failed to select AID {hexlify_string(aid)}")
            else:
                print(f"Error: found card {hexlify(uid)} but unable to select")
                return 
    return 


#Display Menu Functions
def display_start_menu():
    print("\n----Start Menu------------")
    print("Select an option:")
    print("1. CONNECT TO READER")
    print("2. CHANGE SERIAL PORT")
    print("3. CHANGE HF/LF TAG TYPES")
    print("0. EXIT")
    return
   
def display_main_menu():
    print("\n-----Main Menu---------------")
    print("Select an option:")
    print("1. READ CARD UID/CSN")
    print("2. SEND COMMAND")
    print("3. READ MIFARE CLASSIC")
    print("4. WRITE TO MIFARE CLASSIC 1K")
    print("5. Allegion DESFire")
    print("6. PKOC")
    print("0. EXIT")
    print("A. Return to Start Menu")
    return

def display_mifare_read_menu():
    print("\n----MIFARE Read Menu-----")
    print("Select an option:")
    print("1. SET SECTOR AND KEY")
    print("2. READ SECTOR DATA")
    print("0. RETURN TO MAIN MENU")
    return

def display_mifare_write_menu():
    print("\n----MIFARE Write Menu-----")
    print("Select an option:")
    print("1. SET SECTOR AND KEY")
    print("2. SET NEW SECTOR KEY")
    print("3. SET WRITE DATA")
    print("4. WRITE SECTOR DATA")
    print("5. WRITE NEW SECTOR KEY")
    print("0. RETURN TO MAIN MENU")
    return

def display_desfire_menu():
    print("\n----Allegion DESFire Read Menu-----")
    print("Select an option:")
    print("1. SET READ KEY")
    print("2. SET AID")
    print("3. SET FILE NUMBER")
    print("4. SET CRYPTO ENV")
    print("5. READ DATA")
    print("0. RETURN TO MAIN MENU")
    return

def display_pkoc_menu():
    print("\n----PKOC Read Menu-----")
    print("Select an option:")
    print("1. READ CARD")
    print("0. RETURN TO MAIN MENU")
    return

#Menu Functions
def read_mifare_classic(ser):
    sector     = "05"
    sector_key = "FFFFFFFFFFFF"
    key_type   = "00"
    block0     = b'\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'
    block1     = b'\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'
    block2     = b'\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'

    while True:
        print("\n+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++")
        print(f"Sector set to: {sector}")
        print(f"Sector key set to: {hexlify_string(sector_key)}")
        print(f"Key type set to: {key_type}")
        print("\n+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++")
        display_mifare_read_menu()
        choice = input("Enter your choice: ").upper().strip()
        match choice:
            case '0':
                print("Returning to main menu...")
                break
            case '1':
                set_classic_sectorkey(sector, sector_key, key_type)
            case '2':
               block0, block1, block2 = read_mifare_classic_block(ser, sector, sector_key, key_type)
               print(f"Block 1: {hexlify(block0)}")
               print(f"Block 2: {hexlify(block1)}")
               print(f"Block 3: {hexlify(block2)}")
            case _:
                print("Invalid choice. Please select a valid option.")
    return

def write_to_mifare_classic(ser):
    #define MiFare variables
    sector         = "05"
    sector_key     = "FFFFFFFFFFFF"
    new_sector_key = None
    key_type       = "00"
    
    data_to_write  = {1 : "00000000000000000000000000000000", 2: "00000000000000000000000000000000", 3: "00000000000000000000000000000000"}

    while True:
        print("\n+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++")
        print(f"Sector set to: {sector}")
        print(f"Sector key set to: {hexlify_string(sector_key)}")
        print(f"Key type set to: {key_type}")
        print(f"New sector key set to: {hexlify_string(new_sector_key)}")
        print(f"Block 1 data to write: {hexlify_string(data_to_write[1])}")
        print(f"Block 2 data to write: {hexlify_string(data_to_write[2])}")
        print(f"Block 3 data to write: {hexlify_string(data_to_write[3])}")
        print("\n+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++")
        display_mifare_write_menu()
        choice = input("Enter your choice: ").strip()
        match choice:
            case '0': #RETURN TO MAIN MENU
                print("Returning to main menu...")
                break
            case '1': #SET SECTOR AND KEY
                set_classic_sectorkey(sector, sector_key, key_type)            
            case '2': #SET NEW SECTOR KEY
                new_sector_key = set_classic_newkey()
            case '3': #SET WRITE DATA
                data_to_write = set_classic_writedata()
            case '4': #WRITE SECTOR DATA                
                result = write_client_data_to_mifare_classic(ser, sector, sector_key, key_type, data_to_write)
                #sector_hex, sector_key, key_type, new_sector_key, iv, data_to_write = prompt_for_write_inputs()                
            case '5': #WRITE NEW SECTOR KEY
                write_new_mifare_sector_key(ser, sector, sector_key, key_type, new_sector_key)
            case _:
                print("Invalid choice. Please select a valid option.")
    return
   
def main_menu(ser):
    while True:
        try:
            if not ser.is_open:
                ser.open()
                print(f"Serial port {ser.port} opened successfully.")
            display_main_menu()
            choice = input("Enter your choice: ").upper().strip()
            match choice:
                case '0': #Exit
                    print("Exiting...")
                    # Close the serial port
                    if ser.is_open:
                        send_command(ser, LEDOFF % ALLLED.hex())
                        ser.close()
                        print(f"Serial port {ser.port} closed.")
                    sys.exit()
                case '1': #Read Card UID/CSN
                    read_uid(ser)
                case '2': #Send Command
                    sendtocard(ser)
                case '3': #Read MiFare Classic
                    read_mifare_classic(ser)
                case '4': #WRITE TO MIFARE CLASSIC 1K
                    write_to_mifare_classic(ser)
                case '5': #DESFire
                    if ser.is_open:
                        print(f"Serial port {ser.port} opened successfully.")
                        desfire(ser)
                    else:
                        print(f"Failed to open serial port {ser.port}.")
                        break
                case '6': #PKOC
                    if ser.is_open:
                        print(f"Serial port {ser.port} opened successfully.")
                        pkoc(ser)
                    else:
                        print(f"Failed to open serial port {ser.port}.")
                        break
                case 'A': #Return to Start Menu
                    break
                case _:
                    print("Invalid choice. Please select a valid option.")
        except serial.SerialException as e:
            print(f"Serial exception: {e}")
        except ValueError as e:
            print(f"Serial Value Error: {e} ")
        #finally:
            # Close the serial port
        #    if ser.is_open:
        #        ser.close()
        #    print(f"Serial port {ser.port} closed.")
    return
   
def desfire(ser):
    readkey = "00000000000000000000000000000000"
    aid = "000000"
    filenum = "02"
    cryptoenv = CRYTPO_ENV0
    while True:
        print("\n+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++")
        print(f"Read key set to: {hexlify_string(readkey)}")
        print(f"AID set to: {hexlify_string(aid)}")
        print(f"File number set to: {filenum}")
        print(f"Crypto Env set to: {cryptoenv}")
        print("\n+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++")
        display_desfire_menu()
        choice = input("Enter your choice: ").upper().strip()
        match choice:
            case '0': #RETURN TO MAIN MENU
                print("Returning to main menu...")
                break
            case '1': #SET READ KEY
                while True:
                    readkey = input("Enter the read key (16 bytes): ").strip().upper()
                    if is_hex(readkey, 32):
                        break
            case '2': #SET AID
                while True:
                    aid = input("Enter the AID (3 bytes): ").strip().upper()
                    if is_hex(aid, 6):
                        break                
            case '3': #SET FILE NUMBER
                while True:
                    filenum = input("Enter the File Number (1 byte): ").strip().upper()
                    if is_hex(filenum, 2):
                        break
            case '4': #SET CRYPTO ENV
                while True:
                    env = input("Enter the Crypto Env (0, 1, 2, or 3): ").strip().upper()
                    if env in {0,1,2,3}:
                        if env == 0:
                            cryptoenv = CRYTPO_ENV0
                        if env == 1:
                            cryptoenv = CRYTPO_ENV1
                        if env == 2:
                            cryptoenv = CRYTPO_ENV2
                        if env == 3:
                            cryptoenv = CRYTPO_ENV3
                        break
            case '5': #READ DATA
                data = read_desfire_data(ser, readkey, aid, filenum, cryptoenv)
                if data != None:
                    print(f"Data from file {filenum}: {hexlify(data)}")
                else:
                    print(f"Failed to read data from file {filenum}")
            case _:
                print("Invalid choice. Please select a valid option.")   
    return

def pkoc(ser):
    while True:
        display_pkoc_menu()
        choice = input("Enter your choice: ").upper().strip()
        match choice:
            case '0': #RETURN TO MAIN MENU
                print("Returning to main menu...")
                break
            case '1': #Read PKOC
                protover = bytearray()
                data = bytearray()
                uid, mifaretype = read_uid(ser)
                #print(f"Sending command: {PKOC_SELECT}")
                response = send_command(ser, PKOC_SELECT)
                print(f"response: {hexlify(response)}")
                print(f"response[3]: {response[3]}")
                if type(response) == bytearray and response[0:2] == ByteTrue:
                    if response[7:9] == b'\x90\x00': #check for success, last bytes should be 9000
                        if response[3] == 92: #5C in response indicates protocol version
                            protover.extend(response[5:7])
                            print(f"PKOC Protocol Version: {hexlify(protover)}")
                        data.extend(b'\x5C\x02')
                        data.extend(protover)
                        data.extend(b'\x4C\x10') #Transaction Identifier
                        nonce = secrets.token_bytes(16)
                        print(f"nonce: {hexlify(nonce)}")
                        data.extend(nonce) #reader nonce 16 to 65 bytes
                        data.extend(b'\x4D\x20') #reader identifier
                        readerid = secrets.token_bytes(32)
                        data.extend(readerid)
                        print(f"data len: {format(len(readerid), '02X')}")
                        print(f"Reader ID: {hexlify(readerid)}")
                        print(f"TLV: {hexlify(data)}")
                        print(f"Authenticate: {PKOC_AUTHENTICATE % (format(len(data)+6, '02X'), data.hex().upper())}")
                        response = send_command(ser, PKOC_AUTHENTICATE % (format(len(data)+6, '02X'), data.hex().upper()))
                        if type(response) == bytearray and response[0:2] == ByteTrue:
                            if response[136:138] == b'\x90\00':
                                key = response[5:70]
                                sig = response[72:136]
                                print(f"Public Key: {hexlify(response[5:70])}")
                                print(f"\nDigital Signature: {hexlify(sig)}")
                                vk = VerifyingKey.from_string(key, curve=NIST256p)

                                valid = vk.verify(
                                    sig,
                                    nonce,
                                    hashfunc=hashlib.sha256,
                                    sigdecode=sigdecode_string
                                )
                                if valid:
                                    print("Valid signature")
                                    print(f"256 bit credential is: {hexlify(key[1:17])}")
                                    print(f"75 bit credential is:  {hexlify(key[8:17])}")
                                    print(f"64 bit credential is:  {hexlify(key[9:17])}")
                                else:
                                    print("Invalid Signature")
                            else:
                                print(f"Error: {response[len(response)-2:len(response)]}")
                        else:
                            print(f"Error: {response}")
                            
                else:
                    print("Error")
                    
            case _:
                print("Invalid choice. Please select a valid option.")
    return

def main():
    global TAG_TYPES_LF
    global TAG_TYPES_HF
    #get a list of serial ports
    sports = serial.tools.list_ports.comports()
    #set the default to the first port found or None
    if not sports:
        serial_port = None
    else:
        serial_port = sports[0].device
    try:
        #ser = serial.Serial(port=None, baudrate=9600, bytesize=EIGHTBITS, parity=PARITY_NONE, stopbits=STOPBITS_ONE, timeout=None, xonxoff=False, rtscts=False, write_timeout=None, dsrdtr=False, inter_byte_timeout=None, exclusive=None)
        #don't set the port as this will open it and we really should wait until we are interacting with the TWN4
        ser = serial.Serial(timeout=2) #standard comms for Elatec TWN4 are ASCII, CRC off with 9600 baud

        #menu loop
        while True:
            print("\n+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++")
            print(f"serial port set to: {serial_port}")
            print(f"LF tag type set to: {", ".join(map(str, list(TAG_TYPES_LF)))}")
            print(f"HF tag type set to: {", ".join(map(str, list(TAG_TYPES_HF)))}")
            print("\n+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++")
            display_start_menu()
            choice = input("Enter your choice: ").strip()
            match choice:
                case '0': #EXIT
                    print("Exiting...")
                    #make sure to close the serial port if open
                    if ser.is_open:
                        send_command(ser, LEDOFF % ALLLED.hex())
                        ser.close()
                        print(f"Serial port {serial_port} closed.")
                    break
                case '1': #CONNECT TO READER
                    #open the serial port only when the user directs
                    ser.port=serial_port
                    if not ser.is_open:
                        ser.open()  
                        print(f"Serial port {serial_port} opened successfully.")
                        if init_reader(ser, TAG_TYPES_LF, TAG_TYPES_HF):
                            main_menu(ser)
                        else:
                            print("Reader initialization error")
                    else:
                        #skip opening port and init if we are already using it
                        main_menu(ser)
                case '2': #CHANGE SERIAL PORT
                    while True:
                        #get a list of serial ports on the computer
                        ports = serial.tools.list_ports.comports()
                        if not ports:
                            print("No available ports")
                            serial_port = None
                            break
                        print("\n\nAvailable Serial Ports:")         
                        for sport, desc, hwid in sorted(ports):
                            print(f"- {sport}: {desc}")
                        port = input("Enter the serial port: ").strip()
                        valid = False
                        #did we pick a valid port from the list
                        for sport in sorted(ports):
                            if port == sport.device:
                                valid = True
                                break
                        if valid:
                            break
                        else:
                            print("Invalid input. Please enter a valid serial value.")
                    if not serial_port == None:
                        if ser.port is not port: #don't do anything if we picked the same port as before
                             if ser.is_open:
                                ser.close() #close the existing port if open, we are switching to a new device
                                print(f"Serial port {serial_port} closed.")
                             #catch just in case we didn't close port
                             if not ser.is_open:
                                serial_port = "%s" % (port) #set new serial port value
                                print(f"serial port now set to: {serial_port}")
                             else:
                                print(f"Error closing serial port {ser.port}, no change implemented")
                case '3': #CHANGE HF/LF TAG TYPES
                        TAG_TYPES_LF = select_keys_menu(lftagtype)
                        #if len is greater than 1 we have multiple selections check if one is ALL_LFTAGS or NOTAG
                        #if so then ignore the other options as these supersede. ALL supersedes None in this context as well
                        if len(TAG_TYPES_LF) > 1:
                            #check if ALL_LFTAGS selected and if so make TAG_TYPES_LF equal to only ALL_LFTAGS
                            if "ALL_LFTAGS" in TAG_TYPES_LF:
                                TAG_TYPES_LF = {k: lftagtype[k] for k in ['ALL_LFTAGS'] if k in lftagtype}
                            #check if NOTAG selected and if so make TAG_TYPES_LF only equal to NOTAG
                            elif "NOTAG" in TAG_TYPES_LF:
                                TAG_TYPES_LF = {k: lftagtype[k] for k in ['NOTAG'] if k in lftagtype}
                        TAG_TYPES_HF = select_keys_menu(hftagtype)
                        #if len is greater than 1 we have multiple selections check if one is ALL_HFTAGS or NOTAG
                        #if so then ignore the other options as these supersede. ALL supersedes None in this context as well
                        if len(TAG_TYPES_HF) > 1:
                            #check if ALL_HFTAGS selected and if so make TAG_TYPES_HF equal to only ALL_HFTAGS, removing all others
                            if "ALL_HFTAGS" in TAG_TYPES_HF:
                                TAG_TYPES_HF = {k: hftagtype[k] for k in ['ALL_HFTAGS'] if k in hftagtype}
                            #check if NOTAG selected and if so make TAG_TYPES_LF only equal to NOTAG
                            elif "NOTAG" in TAG_TYPES_HF:
                                TAG_TYPES_HF = {k: hftagtype[k] for k in ['NOTAG'] if k in hftagtype}           
                case _:
                        print("Invalid choice. Please select a valid option.")
    except serial.SerialException as e:
        print(f"Serial Exception: {e}")
    except ValueError as e:
        print(f"Serial Value Error: {e} ")
    return

if __name__ == "__main__":
    main()