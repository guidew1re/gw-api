#!/usr/bin/env python3

import argparse
import binascii
import getpass
import os
import struct
import sys
import time
import zlib
from dataclasses import dataclass

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def u16(b, o=0):
    return struct.unpack_from("<H", b, o)[0]


def u32(b, o=0):
    return struct.unpack_from("<I", b, o)[0]


def u64(b, o=0):
    return struct.unpack_from("<Q", b, o)[0]


def s8(b):
    return struct.unpack("<b", b)[0]


def sign_extend(value, size):
    bits = size * 8
    sign = 1 << (bits - 1)
    return (value ^ sign) - sign


def format_bytes(value):
    if value < 0:
        raise ValueError("Byte count must not be negative")

    units = ("B", "KiB", "MiB", "GiB", "TiB", "PiB")
    amount = float(value)

    for unit in units:
        if amount < 1024 or unit == units[-1]:
            if unit == "B":
                return f"{value} B"

            return f"{amount:.2f} {unit}"

        amount /= 1024


def write_all(out, data):
    """Write all bytes, including to streams that perform short writes."""

    view = memoryview(data)

    while view:
        written = out.write(view)

        if written is None:
            raise BlockingIOError("ZIP output stream would block")

        if written <= 0:
            raise IOError("Unable to write ZIP output")

        view = view[written:]


class CountingWriter:
    def __init__(self, out):
        self.out = out
        self.position = 0

    def write(self, data):
        write_all(self.out, data)
        self.position += len(data)


def _make_zipcrypto_crc_table():
    table = []

    for value in range(256):
        crc = value

        for _ in range(8):
            if crc & 1:
                crc = (crc >> 1) ^ 0xEDB88320
            else:
                crc >>= 1

        table.append(crc)

    return tuple(table)


ZIPCRYPTO_CRC_TABLE = _make_zipcrypto_crc_table()


class ZipCryptoEncryptor:
    """Traditional PKZIP encryption, implemented using only the stdlib."""

    def __init__(self, password):
        self.key0 = 0x12345678
        self.key1 = 0x23456789
        self.key2 = 0x34567890

        for value in password:
            self._update_keys(value)

    @staticmethod
    def _crc32_byte(crc, value):
        return (crc >> 8) ^ ZIPCRYPTO_CRC_TABLE[(crc ^ value) & 0xFF]

    def _update_keys(self, value):
        self.key0 = self._crc32_byte(self.key0, value)
        self.key1 = (self.key1 + (self.key0 & 0xFF)) & 0xFFFFFFFF
        self.key1 = (self.key1 * 134775813 + 1) & 0xFFFFFFFF
        self.key2 = self._crc32_byte(self.key2, self.key1 >> 24)

    def encrypt(self, data):
        result = bytearray(len(data))

        for index, value in enumerate(data):
            temp = (self.key2 | 2) & 0xFFFFFFFF
            mask = ((temp * (temp ^ 1)) >> 8) & 0xFF
            result[index] = value ^ mask
            self._update_keys(value)

        return bytes(result)


def dos_datetime(timestamp=None):
    if timestamp is None:
        timestamp = time.time()

    value = time.localtime(timestamp)
    year = min(max(value.tm_year, 1980), 2107)
    dos_date = ((year - 1980) << 9) | (value.tm_mon << 5) | value.tm_mday
    dos_time = (value.tm_hour << 11) | (value.tm_min << 5) | (value.tm_sec // 2)

    return dos_date, dos_time


def deflate_bound(size):
    """Conservative bound used by zlib's deflateBound implementation."""

    return size + (size >> 12) + (size >> 14) + (size >> 25) + 13


def write_encrypted_zip(out, filename, chunks, size, password, level=6):
    """Stream one file into a traditional ZipCrypto-encrypted ZIP archive."""

    if not password:
        raise ValueError("ZIP password must not be empty")

    filename_bytes = filename.encode("utf-8")

    if len(filename_bytes) > 0xFFFF:
        raise ValueError("ZIP entry name is too long")

    # This implementation emits a conventional (non-ZIP64) single-file ZIP.
    # Check before writing so failure never leaves an apparently valid prefix.
    if size < 0 or size > 0xFFFFFFFF:
        raise ValueError("Files of 4 GiB or larger require ZIP64 and are not supported")

    maximum_compressed_size = deflate_bound(size) + 12
    maximum_central_offset = (
        30 + len(filename_bytes) + maximum_compressed_size + 16
    )

    if maximum_central_offset > 0xFFFFFFFF:
        raise ValueError("File is too large for this non-ZIP64 streaming archive")

    writer = CountingWriter(out)
    dos_date, dos_time = dos_datetime()
    flags = 0x0001 | 0x0008 | 0x0800  # encrypted, data descriptor, UTF-8
    method = 8  # raw DEFLATE
    local_offset = writer.position

    local_header = struct.pack(
        "<IHHHHHIIIHH",
        0x04034B50,
        20,
        flags,
        method,
        dos_time,
        dos_date,
        0,
        0,
        0,
        len(filename_bytes),
        0,
    )

    writer.write(local_header)
    writer.write(filename_bytes)

    encryptor = ZipCryptoEncryptor(password)
    encryption_header = os.urandom(11) + bytes([dos_time >> 8])
    writer.write(encryptor.encrypt(encryption_header))

    compressor = zlib.compressobj(level, zlib.DEFLATED, -15)
    crc = 0
    uncompressed_size = 0
    compressed_size = 12  # Traditional encryption header is included.

    for chunk in chunks:
        if not chunk:
            continue

        crc = binascii.crc32(chunk, crc)
        uncompressed_size += len(chunk)

        if uncompressed_size > size:
            raise RuntimeError("File stream is larger than its NTFS metadata")

        compressed = compressor.compress(chunk)

        if compressed:
            encrypted = encryptor.encrypt(compressed)
            writer.write(encrypted)
            compressed_size += len(encrypted)

    compressed = compressor.flush()

    if compressed:
        encrypted = encryptor.encrypt(compressed)
        writer.write(encrypted)
        compressed_size += len(encrypted)

    if uncompressed_size != size:
        raise RuntimeError(
            "File stream size does not match NTFS metadata "
            f"({uncompressed_size}/{size})"
        )

    crc &= 0xFFFFFFFF

    writer.write(
        struct.pack(
            "<IIII",
            0x08074B50,
            crc,
            compressed_size,
            uncompressed_size,
        )
    )

    central_offset = writer.position

    central_header = struct.pack(
        "<IHHHHHHIIIHHHHHII",
        0x02014B50,
        20,
        20,
        flags,
        method,
        dos_time,
        dos_date,
        crc,
        compressed_size,
        uncompressed_size,
        len(filename_bytes),
        0,
        0,
        0,
        0,
        0,
        local_offset,
    )

    writer.write(central_header)
    writer.write(filename_bytes)

    central_size = writer.position - central_offset

    writer.write(
        struct.pack(
            "<IHHHHIIH",
            0x06054B50,
            0,
            0,
            1,
            1,
            central_size,
            central_offset,
            0,
        )
    )

    out.flush()


@dataclass
class Partition:
    index: int
    offset: int
    size: int
    type_name: str = ""


# ---------------------------------------------------------------------------
# Block device
# ---------------------------------------------------------------------------


class BlockDevice:
    def __init__(self, path):
        self.path = path
        self.f = open(path, "rb")
        self.f.seek(0, os.SEEK_END)
        self.size = self.f.tell()

    def read(self, offset, size):
        if offset < 0 or offset + size > self.size:
            raise IOError(f"Read outside image: offset={offset:#x}, size={size:#x}")

        self.f.seek(offset)
        data = self.f.read(size)

        if len(data) != size:
            raise IOError(
                f"Short read at offset {offset:#x}: requested {size}, got {len(data)}"
            )

        return data

    def close(self):
        self.f.close()


# ---------------------------------------------------------------------------
# VMware descriptor handling
# ---------------------------------------------------------------------------


def resolve_vmdk(path):
    """
    Supports:

      * Raw/flat disk image
      * Text VMDK descriptor referencing a single FLAT extent

    Returns the sector-addressable backing file.
    """

    with open(path, "rb") as f:
        head = f.read(65536)

    # VMware sparse/monolithic binary VMDK magic.
    if head[:4] == b"KDMV":
        raise RuntimeError(
            "VMware sparse/monolithic VMDK detected. "
            "This reader currently supports flat/raw extents only."
        )

    try:
        text = head.decode("ascii")
    except UnicodeDecodeError:
        # Probably already a raw/flat image.
        return path

    if "Disk DescriptorFile" not in text and "createType" not in text:
        return path

    extents = []

    for line in text.splitlines():
        line = line.strip()

        if not line or line.startswith("#"):
            continue

        # Typical example:
        #
        # RW 41922560 FLAT "machine-flat.vmdk" 0
        #
        parts = line.split()

        if len(parts) < 4:
            continue

        access = parts[0].upper()
        extent_type = parts[2].upper()

        if access not in ("RW", "RDONLY", "NOACCESS"):
            continue

        if extent_type != "FLAT":
            continue

        sectors = int(parts[1])
        filename = parts[3].strip('"')

        sector_offset = 0

        if len(parts) >= 5:
            try:
                sector_offset = int(parts[4])
            except ValueError:
                sector_offset = 0

        extents.append(
            (
                sectors,
                filename,
                sector_offset,
            )
        )

    if not extents:
        raise RuntimeError(
            "VMDK descriptor found, but no supported FLAT extent was found."
        )

    if len(extents) != 1:
        raise RuntimeError(
            "This version supports a single FLAT extent only. "
            f"Descriptor contains {len(extents)} extents."
        )

    _, filename, sector_offset = extents[0]

    if sector_offset != 0:
        raise RuntimeError(
            "FLAT extent with a non-zero sector offset is not currently supported."
        )

    backing = os.path.join(
        os.path.dirname(os.path.abspath(path)),
        filename,
    )

    if not os.path.isfile(backing):
        raise FileNotFoundError(
            f"Flat extent referenced by descriptor was not found: {backing}"
        )

    return backing


# ---------------------------------------------------------------------------
# Partition tables
# ---------------------------------------------------------------------------


def parse_mbr(dev):
    sector = dev.read(0, 512)

    if sector[510:512] != b"\x55\xaa":
        raise RuntimeError("No valid MBR signature found")

    entries = []

    for slot in range(4):
        off = 446 + slot * 16

        ptype = sector[off + 4]
        start_lba = u32(sector, off + 8)
        sector_count = u32(sector, off + 12)

        if ptype == 0 or sector_count == 0:
            continue

        entries.append(
            (
                slot,
                ptype,
                start_lba,
                sector_count,
            )
        )

    return entries


def parse_gpt(dev):
    # GPT header normally begins at LBA 1.
    hdr = dev.read(512, 512)

    if hdr[:8] != b"EFI PART":
        return None

    header_size = u32(hdr, 12)

    if header_size < 92 or header_size > 512:
        raise RuntimeError(f"Invalid GPT header size: {header_size}")

    entry_lba = u64(hdr, 72)
    entry_count = u32(hdr, 80)
    entry_size = u32(hdr, 84)

    if entry_size < 128:
        raise RuntimeError(f"Unsupported GPT entry size: {entry_size}")

    # Avoid absurd allocations if metadata is corrupt.
    entry_count = min(entry_count, 4096)

    total = entry_count * entry_size

    table = dev.read(
        entry_lba * 512,
        total,
    )

    partitions = []
    visible_index = 0

    for i in range(entry_count):
        off = i * entry_size
        ent = table[off : off + entry_size]

        type_guid = ent[:16]

        # Empty GPT entry.
        if type_guid == b"\x00" * 16:
            continue

        first_lba = u64(ent, 32)
        last_lba = u64(ent, 40)

        if last_lba < first_lba:
            continue

        name_bytes = ent[56 : min(128, len(ent))]

        try:
            name = name_bytes.decode(
                "utf-16le",
                errors="ignore",
            ).rstrip("\x00")
        except Exception:
            name = ""

        partitions.append(
            Partition(
                index=visible_index,
                offset=first_lba * 512,
                size=(last_lba - first_lba + 1) * 512,
                type_name=name or "GPT partition",
            )
        )

        visible_index += 1

    return partitions


def get_partitions(dev):
    mbr = parse_mbr(dev)

    protective = any(ptype == 0xEE for _, ptype, _, _ in mbr)

    if protective:
        gpt = parse_gpt(dev)

        if gpt is None:
            raise RuntimeError("Protective MBR exists but GPT could not be parsed")

        return gpt

    result = []

    for visible, (
        _,
        ptype,
        start,
        count,
    ) in enumerate(mbr):
        result.append(
            Partition(
                index=visible,
                offset=start * 512,
                size=count * 512,
                type_name=f"MBR type {ptype:#04x}",
            )
        )

    return result


# ---------------------------------------------------------------------------
# NTFS
# ---------------------------------------------------------------------------


class NTFS:
    ATTR_STANDARD_INFORMATION = 0x10
    ATTR_ATTRIBUTE_LIST = 0x20
    ATTR_FILE_NAME = 0x30
    ATTR_DATA = 0x80
    ATTR_END = 0xFFFFFFFF

    def __init__(self, dev, partition):
        self.dev = dev
        self.partition = partition

        boot = self.read_partition(
            0,
            512,
        )

        if boot[3:11] != b"NTFS    ":
            raise RuntimeError(f"Partition {partition.index} is not NTFS")

        self.bytes_per_sector = u16(
            boot,
            11,
        )

        self.sectors_per_cluster = boot[13]

        if self.bytes_per_sector == 0 or self.sectors_per_cluster == 0:
            raise RuntimeError("Invalid NTFS boot sector")

        self.cluster_size = self.bytes_per_sector * self.sectors_per_cluster

        self.mft_lcn = u64(
            boot,
            48,
        )

        record_code = s8(boot[64:65])

        if record_code < 0:
            self.record_size = 1 << (-record_code)
        else:
            self.record_size = record_code * self.cluster_size

        if self.record_size <= 0:
            raise RuntimeError("Invalid NTFS MFT record size")

        self.mft_offset = self.mft_lcn * self.cluster_size

        self.mft_runs = None
        self.mft_size = None

        self._initialize_mft()

    # -------------------------------------------------------------------
    # Basic reads
    # -------------------------------------------------------------------

    def read_partition(
        self,
        offset,
        size,
    ):
        if offset < 0 or size < 0 or offset + size > self.partition.size:
            raise IOError("Read outside partition")

        return self.dev.read(
            self.partition.offset + offset,
            size,
        )

    # -------------------------------------------------------------------
    # FILE record fixups
    # -------------------------------------------------------------------

    def apply_fixup(
        self,
        record,
    ):
        record = bytearray(record)

        if record[:4] != b"FILE":
            return None

        usa_offset = u16(
            record,
            4,
        )

        usa_count = u16(
            record,
            6,
        )

        if usa_count < 1:
            return None

        if usa_offset + usa_count * 2 > len(record):
            return None

        usn = record[usa_offset : usa_offset + 2]

        replacements = []

        for i in range(
            1,
            usa_count,
        ):
            p = usa_offset + i * 2

            replacements.append(record[p : p + 2])

        for i, replacement in enumerate(
            replacements,
            1,
        ):
            sector_end = i * self.bytes_per_sector - 2

            if sector_end + 2 > len(record):
                return None

            if record[sector_end : sector_end + 2] != usn:
                return None

            record[sector_end : sector_end + 2] = replacement

        return bytes(record)

    # -------------------------------------------------------------------
    # Attributes
    # -------------------------------------------------------------------

    def attributes(
        self,
        record,
    ):
        first = u16(
            record,
            20,
        )

        off = first

        while off + 16 <= len(record):
            attr_type = u32(
                record,
                off,
            )

            if attr_type == self.ATTR_END:
                break

            length = u32(
                record,
                off + 4,
            )

            if length < 16 or off + length > len(record):
                break

            nonresident = record[off + 8]

            name_len = record[off + 9]

            name_off = u16(
                record,
                off + 10,
            )

            name = ""

            if name_len:
                start = off + name_off

                end = start + name_len * 2

                if end <= off + length:
                    name = record[start:end].decode(
                        "utf-16le",
                        errors="replace",
                    )

            yield {
                "type": attr_type,
                "offset": off,
                "length": length,
                "nonresident": bool(nonresident),
                "name": name,
                "raw": record[off : off + length],
            }

            off += length

    def resident_value(
        self,
        attr,
    ):
        raw = attr["raw"]

        if len(raw) < 24:
            raise RuntimeError("Invalid resident attribute")

        length = u32(
            raw,
            16,
        )

        offset = u16(
            raw,
            20,
        )

        if offset + length > len(raw):
            raise RuntimeError("Invalid resident attribute")

        return raw[offset : offset + length]

    # -------------------------------------------------------------------
    # Runlists
    # -------------------------------------------------------------------

    def parse_runlist(
        self,
        attr,
    ):
        raw = attr["raw"]

        if not attr["nonresident"]:
            raise RuntimeError("Attribute is resident")

        if len(raw) < 64:
            raise RuntimeError("Invalid non-resident attribute")

        run_offset = u16(
            raw,
            32,
        )

        if run_offset == 0 or run_offset >= len(raw):
            raise RuntimeError("Invalid runlist offset")

        data = raw[run_offset:]

        pos = 0
        current_lcn = 0

        runs = []

        while pos < len(data):
            header = data[pos]
            pos += 1

            if header == 0:
                break

            len_size = header & 0x0F

            off_size = header >> 4

            if len_size == 0:
                raise RuntimeError("Invalid NTFS run")

            if pos + len_size + off_size > len(data):
                raise RuntimeError("Truncated NTFS runlist")

            run_length = int.from_bytes(
                data[pos : pos + len_size],
                "little",
            )

            pos += len_size

            # off_size == 0 means a sparse run.
            if off_size == 0:
                runs.append(
                    (
                        None,
                        run_length,
                    )
                )

                continue

            encoded = int.from_bytes(
                data[pos : pos + off_size],
                "little",
            )

            delta = sign_extend(
                encoded,
                off_size,
            )

            pos += off_size

            current_lcn += delta

            if current_lcn < 0:
                raise RuntimeError("Invalid negative LCN")

            runs.append(
                (
                    current_lcn,
                    run_length,
                )
            )

        return runs

    # -------------------------------------------------------------------
    # Reading non-resident streams
    # -------------------------------------------------------------------

    def read_runs(
        self,
        runs,
        logical_size=None,
    ):
        remaining = logical_size

        for lcn, clusters in runs:
            byte_count = clusters * self.cluster_size

            if remaining is not None:
                byte_count = min(
                    byte_count,
                    remaining,
                )

            if byte_count <= 0:
                break

            if lcn is None:
                # Sparse run. Avoid allocating the entire
                # run if it is huge.
                left = byte_count

                zero_chunk = b"\x00" * min(
                    1024 * 1024,
                    byte_count,
                )

                while left:
                    amount = min(
                        left,
                        len(zero_chunk),
                    )

                    yield zero_chunk[:amount]

                    left -= amount

            else:
                offset = lcn * self.cluster_size

                left = byte_count

                while left:
                    amount = min(
                        left,
                        1024 * 1024,
                    )

                    yield self.read_partition(
                        offset,
                        amount,
                    )

                    offset += amount
                    left -= amount

            if remaining is not None:
                remaining -= byte_count

                if remaining <= 0:
                    break

    def nonresident_sizes(
        self,
        attr,
    ):
        raw = attr["raw"]

        if len(raw) < 64:
            raise RuntimeError("Invalid non-resident attribute")

        allocated = u64(
            raw,
            40,
        )

        real = u64(
            raw,
            48,
        )

        initialized = u64(
            raw,
            56,
        )

        return (
            allocated,
            real,
            initialized,
        )

    # -------------------------------------------------------------------
    # $MFT handling
    # -------------------------------------------------------------------

    def _initialize_mft(self):
        # MFT record zero is initially reachable directly
        # from the LCN specified in the boot sector.

        raw = self.read_partition(
            self.mft_offset,
            self.record_size,
        )

        record = self.apply_fixup(raw)

        if record is None:
            raise RuntimeError("Unable to parse NTFS $MFT record zero")

        data_attrs = []

        for attr in self.attributes(record):
            if attr["type"] == self.ATTR_DATA and attr["name"] == "":
                data_attrs.append(attr)

        if not data_attrs:
            raise RuntimeError("Unable to locate $MFT data attribute")

        # Minimal implementation:
        # expect the base $DATA attribute to contain
        # the required MFT runlist.
        attr = data_attrs[0]

        if not attr["nonresident"]:
            raise RuntimeError("Unexpected resident $MFT data")

        self.mft_runs = self.parse_runlist(attr)

        _, real, _ = self.nonresident_sizes(attr)

        self.mft_size = real

    def mft_read(
        self,
        offset,
        size,
    ):
        """
        Read bytes from the logical $MFT stream.
        """

        result = bytearray()

        logical_start = 0
        wanted_start = offset
        wanted_end = offset + size

        for lcn, clusters in self.mft_runs:
            run_bytes = clusters * self.cluster_size

            logical_end = logical_start + run_bytes

            if wanted_end <= logical_start:
                break

            if wanted_start < logical_end and wanted_end > logical_start:
                overlap_start = max(
                    wanted_start,
                    logical_start,
                )

                overlap_end = min(
                    wanted_end,
                    logical_end,
                )

                within_run = overlap_start - logical_start

                amount = overlap_end - overlap_start

                if lcn is None:
                    result.extend(b"\x00" * amount)

                else:
                    physical = lcn * self.cluster_size + within_run

                    result.extend(
                        self.read_partition(
                            physical,
                            amount,
                        )
                    )

            logical_start = logical_end

        if len(result) != size:
            raise IOError(f"Unable to read requested MFT range ({len(result)}/{size})")

        return bytes(result)

    def get_record(
        self,
        number,
    ):
        offset = number * self.record_size

        if offset + self.record_size > self.mft_size:
            return None

        raw = self.mft_read(
            offset,
            self.record_size,
        )

        return self.apply_fixup(raw)

    # -------------------------------------------------------------------
    # FILE_NAME handling
    # -------------------------------------------------------------------

    def get_names(
        self,
        record,
    ):
        names = []

        for attr in self.attributes(record):
            if attr["type"] != self.ATTR_FILE_NAME:
                continue

            if attr["nonresident"]:
                continue

            value = self.resident_value(attr)

            if len(value) < 66:
                continue

            parent_ref = u64(
                value,
                0,
            )

            parent_record = parent_ref & 0x0000FFFFFFFFFFFF

            name_len = value[64]
            namespace = value[65]

            end = 66 + name_len * 2

            if end > len(value):
                continue

            name = value[66:end].decode(
                "utf-16le",
                errors="replace",
            )

            names.append(
                (
                    name,
                    parent_record,
                    namespace,
                )
            )

        return names

    def record_in_use(
        self,
        record,
    ):
        flags = u16(
            record,
            22,
        )

        return bool(flags & 1)

    def record_is_directory(
        self,
        record,
    ):
        flags = u16(
            record,
            22,
        )

        return bool(flags & 2)

    # -------------------------------------------------------------------
    # Path lookup
    # -------------------------------------------------------------------

    def build_name_index(
        self,
    ):
        """
        Scan the MFT and create:

            parent_record ->
                [(name, child_record), ...]

        This avoids implementing NTFS directory
        indexes ($INDEX_ROOT/$INDEX_ALLOCATION).
        """

        index = {}

        count = self.mft_size // self.record_size

        for number in range(count):
            try:
                record = self.get_record(number)
            except Exception:
                continue

            if record is None:
                continue

            if not self.record_in_use(record):
                continue

            for (
                name,
                parent,
                namespace,
            ) in self.get_names(record):
                # Namespace 2 is DOS/8.3 only.
                # Prefer Win32/POSIX names.
                if namespace == 2:
                    continue

                index.setdefault(
                    parent,
                    [],
                ).append(
                    (
                        name,
                        number,
                    )
                )

        return index

    def find_path(
        self,
        path,
    ):
        parts = [
            p
            for p in path.replace(
                "/",
                "\\",
            ).split("\\")
            if p
        ]

        # NTFS root directory is normally
        # MFT record 5.
        current = 5

        index = self.build_name_index()

        for component in parts:
            component_folded = component.casefold()

            found = None

            for (
                name,
                child,
            ) in index.get(
                current,
                [],
            ):
                if name.casefold() == component_folded:
                    found = child
                    break

            if found is None:
                raise FileNotFoundError(path)

            current = found

        record = self.get_record(current)

        if record is None:
            raise FileNotFoundError(path)

        return (
            current,
            record,
        )

    # -------------------------------------------------------------------
    # File streaming
    # -------------------------------------------------------------------

    def file_size(
        self,
        record,
    ):
        data_attrs = [
            attr
            for attr in self.attributes(record)
            if attr["type"] == self.ATTR_DATA and attr["name"] == ""
        ]

        if not data_attrs:
            raise RuntimeError("File has no unnamed $DATA attribute")

        if len(data_attrs) == 1 and not data_attrs[0]["nonresident"]:
            return len(self.resident_value(data_attrs[0]))

        real_sizes = []

        for attr in data_attrs:
            if attr["nonresident"]:
                _, real, _ = self.nonresident_sizes(attr)
                real_sizes.append(real)

        if not real_sizes:
            raise RuntimeError("Unable to determine file $DATA stream size")

        return max(real_sizes)

    def stream_file(
        self,
        record,
    ):
        data_attrs = []

        for attr in self.attributes(record):
            if attr["type"] != self.ATTR_DATA:
                continue

            # Ignore alternate data streams.
            if attr["name"]:
                continue

            data_attrs.append(attr)

        if not data_attrs:
            raise RuntimeError("File has no unnamed $DATA attribute")

        # Simple resident file.
        if len(data_attrs) == 1 and not data_attrs[0]["nonresident"]:
            yield self.resident_value(data_attrs[0])

            return

        # Collect non-resident extents by starting VCN.
        extents = []

        real_size = None

        for attr in data_attrs:
            if not attr["nonresident"]:
                continue

            raw = attr["raw"]

            if len(raw) < 64:
                raise RuntimeError("Invalid non-resident $DATA attribute")

            flags = u16(
                raw,
                12,
            )

            # 0x0001 = compressed
            # 0x4000 = encrypted
            if flags & 0x0001:
                raise RuntimeError("NTFS-compressed files are not supported")

            if flags & 0x4000:
                raise RuntimeError("EFS-encrypted files are not supported")

            start_vcn = u64(
                raw,
                16,
            )

            runs = self.parse_runlist(attr)

            _, attr_real_size, _ = self.nonresident_sizes(attr)

            if real_size is None or attr_real_size > real_size:
                real_size = attr_real_size

            extents.append(
                (
                    start_vcn,
                    runs,
                )
            )

        if not extents:
            raise RuntimeError("Unable to read file $DATA stream")

        extents.sort(key=lambda x: x[0])

        # Merge the runlists in VCN order.
        all_runs = []

        for _, runs in extents:
            all_runs.extend(runs)

        yield from self.read_runs(
            all_runs,
            logical_size=real_size,
        )


# ---------------------------------------------------------------------------
# Commands
# ---------------------------------------------------------------------------


def cmd_partitions(
    args,
):
    backing = resolve_vmdk(args.image)

    dev = BlockDevice(backing)

    try:
        partitions = get_partitions(dev)

        if not partitions:
            print("No partitions detected.")

            return

        for p in partitions:
            # Probe the filesystem signature where possible.
            filesystem = ""

            try:
                boot = dev.read(
                    p.offset,
                    min(
                        512,
                        p.size,
                    ),
                )

                if len(boot) >= 11 and boot[3:11] == b"NTFS    ":
                    filesystem = "NTFS"

                elif len(boot) >= 90 and (boot[82:90] == b"FAT32   "):
                    filesystem = "FAT32"

            except Exception:
                pass

            print(
                f"{p.index}: "
                f"offset={p.offset} ({format_bytes(p.offset)}) "
                f"size={p.size} ({format_bytes(p.size)}) "
                f"type={p.type_name}"
                + (f" filesystem={filesystem}" if filesystem else "")
            )

    finally:
        dev.close()


def cmd_extract(
    args,
):
    backing = resolve_vmdk(args.image)

    dev = BlockDevice(backing)

    try:
        partitions = get_partitions(dev)

        if args.partition < 0 or args.partition >= len(partitions):
            raise RuntimeError(
                f"Partition index "
                f"{args.partition} "
                f"does not exist. "
                f"Detected "
                f"{len(partitions)} "
                f"partition(s)."
            )

        partition = partitions[args.partition]

        ntfs = NTFS(
            dev,
            partition,
        )

        _, record = ntfs.find_path(args.path)

        if ntfs.record_is_directory(record):
            raise IsADirectoryError(args.path)

        out = sys.stdout.buffer

        for chunk in ntfs.stream_file(record):
            out.write(chunk)

        out.flush()

    finally:
        dev.close()


def zip_entry_name(path, requested_name=None):
    if requested_name is None:
        normalized = path.replace("\\", "/").rstrip("/")
        requested_name = normalized.rsplit("/", 1)[-1]

    name = requested_name.replace("\\", "/")
    parts = name.split("/")

    if (
        not name
        or name.startswith("/")
        or any(part in ("", ".", "..") for part in parts)
    ):
        raise ValueError("ZIP entry name must be a safe relative path")

    return name


def zip_password(args):
    if args.password is not None:
        value = args.password
    else:
        env_name = args.password_env or "VMDKREAD_PASSWORD"
        value = os.environ.get(env_name)

        if value is None and args.password_env:
            raise RuntimeError(f"Password environment variable is not set: {env_name}")

        if value is None:
            value = getpass.getpass("ZIP password: ")

    if not value:
        raise ValueError("ZIP password must not be empty")

    return value.encode("utf-8")


def cmd_zip(
    args,
):
    password = zip_password(args)
    entry_name = zip_entry_name(args.path, args.name)
    backing = resolve_vmdk(args.image)
    dev = BlockDevice(backing)

    try:
        partitions = get_partitions(dev)

        if args.partition < 0 or args.partition >= len(partitions):
            raise RuntimeError(
                f"Partition index "
                f"{args.partition} "
                f"does not exist. "
                f"Detected "
                f"{len(partitions)} "
                f"partition(s)."
            )

        ntfs = NTFS(dev, partitions[args.partition])
        _, record = ntfs.find_path(args.path)

        if ntfs.record_is_directory(record):
            raise IsADirectoryError(args.path)

        output = sys.stdout.buffer
        close_output = False

        if args.output != "-":
            output_path = os.path.abspath(args.output)
            input_paths = {
                os.path.normcase(os.path.abspath(args.image)),
                os.path.normcase(os.path.abspath(backing)),
            }

            if os.path.normcase(output_path) in input_paths:
                raise ValueError("ZIP output must not overwrite the disk image")

            # Refuse to replace an existing file. This also prevents an
            # accidental partial archive from destroying useful data.
            output = open(output_path, "xb")
            close_output = True

        try:
            write_encrypted_zip(
                output,
                entry_name,
                ntfs.stream_file(record),
                ntfs.file_size(record),
                password,
                level=args.level,
            )
        finally:
            if close_output:
                output.close()

    finally:
        dev.close()


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def build_parser():
    parser = argparse.ArgumentParser(
        prog="vmdkread.py",
        description=("Read NTFS files directly from flat/raw VMware disk images."),
    )

    subparsers = parser.add_subparsers(
        dest="command",
        required=True,
        metavar="COMMAND",
    )

    # -------------------------------------------------------------------
    # partitions
    # -------------------------------------------------------------------

    p_partitions = subparsers.add_parser(
        "partitions",
        help=("List partitions in the disk image"),
    )

    p_partitions.add_argument(
        "image",
        help=("VMDK descriptor, flat VMDK, or raw image"),
    )

    p_partitions.set_defaults(func=cmd_partitions)

    # -------------------------------------------------------------------
    # extract
    # -------------------------------------------------------------------

    p_extract = subparsers.add_parser(
        "extract",
        help=("Write a file from an NTFS partition to stdout"),
    )

    p_extract.add_argument(
        "image",
        help=("VMDK descriptor, flat VMDK, or raw image"),
    )

    p_extract.add_argument(
        "partition",
        type=int,
        help=("Zero-based partition index"),
    )

    p_extract.add_argument(
        "path",
        help=(
            "NTFS path, for example "
            r'"\Windows\System32\drivers\etc\hosts"'
        ),
    )

    p_extract.set_defaults(func=cmd_extract)

    # -------------------------------------------------------------------
    # zip
    # -------------------------------------------------------------------

    p_zip = subparsers.add_parser(
        "zip",
        help=("Stream a file as a password-protected ZIP to stdout"),
        description=(
            "Read one NTFS file, compress it, encrypt it using traditional "
            "ZipCrypto, and write the ZIP archive to stdout without creating "
            "an intermediate extracted file."
        ),
    )

    p_zip.add_argument(
        "image",
        help=("VMDK descriptor, flat VMDK, or raw image"),
    )

    p_zip.add_argument(
        "partition",
        type=int,
        help=("Zero-based partition index"),
    )

    p_zip.add_argument(
        "path",
        help=("NTFS path of the file to archive"),
    )

    p_zip.add_argument(
        "-o",
        "--output",
        default="-",
        help=(
            "Write the final ZIP directly to FILE; use - for stdout "
            "(default: -). Existing files are not overwritten."
        ),
    )

    p_zip.add_argument(
        "--rename",
        "--name",
        dest="name",
        metavar="ARCHIVE_PATH",
        help=(
            "Rename the file inside the ZIP, optionally including a relative "
            "path (default: source basename)"
        ),
    )

    password_group = p_zip.add_mutually_exclusive_group()

    password_group.add_argument(
        "--password",
        help=("ZIP password (visible in the process list; prompting is safer)"),
    )

    password_group.add_argument(
        "--password-env",
        metavar="NAME",
        help=(
            "Read the password from environment variable NAME "
            "(default lookup: VMDKREAD_PASSWORD, then prompt)"
        ),
    )

    p_zip.add_argument(
        "--level",
        type=int,
        choices=range(0, 10),
        default=6,
        metavar="0-9",
        help=("DEFLATE compression level (default: 6)"),
    )

    p_zip.set_defaults(func=cmd_zip)

    return parser


def main():
    parser = build_parser()

    args = parser.parse_args()

    args.func(args)


if __name__ == "__main__":
    try:
        main()

    except BrokenPipeError:
        # Expected when stdout is piped to a process
        # that closes its input before we finish.
        try:
            sys.stdout.close()
        except Exception:
            pass

    except KeyboardInterrupt:
        print(
            "Interrupted.",
            file=sys.stderr,
        )
        sys.exit(130)

    except Exception as exc:
        print(
            f"error: {exc}",
            file=sys.stderr,
        )
        sys.exit(1)
