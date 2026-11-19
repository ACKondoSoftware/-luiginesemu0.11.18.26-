#!python3.15
"""luigines emu 0.1.1 — single-file NES emulator (full 2A03 opcode set, 70+ mappers)"""
from __future__ import annotations

import ctypes
import ctypes.util
import math
import os
import sys
import threading
import time
import tkinter as tk
from collections import deque
from tkinter import filedialog, messagebox

# =============================================================================
#  PALETTE - 64 NES colors (RGB) blue-tinted per request
# =============================================================================

_NES_PAL = (
    (0x66,0x66,0x66),(0x00,0x2A,0x88),(0x14,0x12,0xA7),(0x3B,0x00,0xA4),
    (0x5C,0x00,0x7E),(0x6E,0x00,0x40),(0x6C,0x06,0x00),(0x56,0x1D,0x00),
    (0x33,0x35,0x00),(0x0B,0x48,0x00),(0x00,0x52,0x00),(0x00,0x4F,0x08),
    (0x00,0x40,0x4D),(0x00,0x00,0x00),(0x00,0x00,0x00),(0x00,0x00,0x00),
    (0xAD,0xAD,0xAD),(0x15,0x5F,0xD9),(0x42,0x40,0xFF),(0x75,0x27,0xFE),
    (0xA0,0x1A,0xCC),(0xB7,0x1E,0x7B),(0xB5,0x31,0x20),(0x99,0x4E,0x00),
    (0x6B,0x6D,0x00),(0x38,0x87,0x00),(0x0C,0x93,0x00),(0x00,0x8F,0x32),
    (0x00,0x7C,0x8D),(0x00,0x00,0x00),(0x00,0x00,0x00),(0x00,0x00,0x00),
    (0xFF,0xFE,0xFF),(0x64,0xB0,0xFF),(0x92,0x90,0xFF),(0xC6,0x76,0xFF),
    (0xF3,0x6A,0xFF),(0xFE,0x6E,0xCC),(0xFE,0x81,0x70),(0xEA,0x9E,0x22),
    (0xBC,0xBE,0x00),(0x88,0xD8,0x00),(0x5C,0xE4,0x30),(0x45,0xE0,0x82),
    (0x48,0xCD,0xDE),(0x4F,0x4F,0x4F),(0x00,0x00,0x00),(0x00,0x00,0x00),
    (0xFF,0xFE,0xFF),(0xC0,0xDF,0xFF),(0xD3,0xD2,0xFF),(0xE8,0xC8,0xFF),
    (0xFB,0xC2,0xFF),(0xFE,0xC4,0xEA),(0xFE,0xCC,0xC5),(0xF7,0xD8,0xA5),
    (0xE4,0xE5,0x94),(0xCF,0xEF,0x96),(0xBD,0xF4,0xAB),(0xB3,0xF3,0xCC),
    (0xB5,0xEB,0xF2),(0xB8,0xB8,0xB8),(0x00,0x00,0x00),(0x00,0x00,0x00),
)


def _blue_tint(rgb):
    r, g, b = rgb
    r = int(r * 0.55)
    g = int(g * 0.75)
    b = min(255, int(b * 1.10) + 35)
    return (r, g, b)


NES_PALETTE_RGB = tuple(_blue_tint(c) for c in _NES_PAL)
NES_PALETTE_HEX = tuple("#%02x%02x%02x" % c for c in NES_PALETTE_RGB)
NES_PALETTE_BYTES = tuple(bytes(c) for c in NES_PALETTE_RGB)


# =============================================================================
#  iNES / NES 2.0 loader  - accepts every valid header (incl. DiskDude! junk)
# =============================================================================

class INESHeader:
    __slots__ = ("prg_banks", "chr_banks", "mapper", "mirroring", "battery",
                 "trainer", "four_screen", "is_nes2", "submapper", "prg_ram",
                 "prg_nvram", "chr_ram", "tv_system", "filename", "title")

    def __init__(self, data, filename=""):
        if len(data) < 16 or data[0:4] != b"NES\x1a":
            raise ValueError("Not a valid iNES file (missing NES<EOF> magic)")
        self.filename = filename
        self.title = os.path.basename(filename) if filename else "untitled"
        self.prg_banks = data[4]
        self.chr_banks = data[5]
        f6, f7 = data[6], data[7]
        self.mirroring = "vertical" if (f6 & 1) else "horizontal"
        self.battery = bool(f6 & 2)
        self.trainer = bool(f6 & 4)
        self.four_screen = bool(f6 & 8)
        self.is_nes2 = ((f7 >> 2) & 3) == 2
        self.prg_nvram = 0
        self.chr_ram = 0
        if self.is_nes2:
            self.mapper = (f6 >> 4) | (f7 & 0xF0) | ((data[8] & 0x0F) << 8)
            self.submapper = data[8] >> 4
            prg_hi = data[9] & 0x0F
            chr_hi = data[9] >> 4
            if prg_hi == 0xF:
                size = (1 << (data[4] >> 2)) * ((data[4] & 3) * 2 + 1)
                self.prg_banks = max(1, size // 16384)
            else:
                self.prg_banks |= prg_hi << 8
            if chr_hi == 0xF:
                size = (1 << (data[5] >> 2)) * ((data[5] & 3) * 2 + 1)
                self.chr_banks = size // 8192
            else:
                self.chr_banks |= chr_hi << 8
            lo, hi = data[10] & 0x0F, data[10] >> 4
            self.prg_ram = (64 << lo) if lo else 0
            self.prg_nvram = (64 << hi) if hi else 0
            lo, hi = data[11] & 0x0F, data[11] >> 4
            self.chr_ram = ((64 << lo) if lo else 0) + ((64 << hi) if hi else 0)
            self.tv_system = "PAL" if (data[12] & 3) == 1 else "NTSC"
        else:
            junk = any(data[12:16])
            if junk:
                f7 = 0
            self.mapper = (f6 >> 4) | (f7 & 0xF0)
            self.submapper = 0
            self.prg_ram = data[8] * 8192 if (data[8] and not junk) else 8192
            self.tv_system = "PAL" if (data[9] & 1 and not junk) else "NTSC"


class ROM:
    def __init__(self, path):
        with open(path, "rb") as f:
            data = f.read()
        self.header = h = INESHeader(data, path)
        off = 16
        if h.trainer:
            self.trainer = data[off:off + 512]
            off += 512
        else:
            self.trainer = b""
        prg_size = h.prg_banks * 16384
        chr_size = h.chr_banks * 8192
        if prg_size == 0:
            raise ValueError("ROM declares no PRG data")
        self.prg = bytearray(data[off:off + prg_size])
        if len(self.prg) < prg_size:
            self.prg.extend(bytes(prg_size - len(self.prg)))
        if len(self.prg) % 8192:
            self.prg.extend(bytes(8192 - len(self.prg) % 8192))
        off += prg_size
        if chr_size > 0:
            self.chr = bytearray(data[off:off + chr_size])
            if len(self.chr) < chr_size:
                self.chr.extend(bytes(chr_size - len(self.chr)))
            self.has_chr_ram = False
        else:
            self.chr = bytearray(max(8192, h.chr_ram))
            self.has_chr_ram = True


# =============================================================================
#  Mappers - shared 8K-PRG / 1K-CHR / 1K-nametable banking core
# =============================================================================

_MIRROR4 = ("vertical", "horizontal", "one-screen-lo", "one-screen-hi")


class Mapper:
    needs_cpu_clock = False
    has_audio = False
    split_chr = False
    exram_mode = 0

    def __init__(self, rom):
        h = rom.header
        self.rom = rom
        self.header = h
        self.prg = rom.prg
        self.chr = rom.chr
        self.chr_writable = rom.has_chr_ram
        ram = max(8192, (h.prg_ram or 0) + (h.prg_nvram or 0))
        ram = (ram + 8191) & ~8191
        self.prg_ram = bytearray(ram)
        self.prg_ram_enabled = True
        self.prg_ram_writable = True
        self.irq_pending = False
        self.cpu = None
        self.prg_count8 = max(1, len(self.prg) >> 13)
        self.chr_count1 = max(1, len(self.chr) >> 10)
        self.prg_map = [0, 0, 0, 0]
        self.chr_map = [0] * 8
        self.ciram = bytearray(4096)
        view = memoryview(self.ciram)
        self._ci = tuple(view[i * 1024:(i + 1) * 1024] for i in range(4))
        self.four_screen = h.four_screen
        self._mirroring = ""
        self.nt = [self._ci[0], self._ci[0], self._ci[1], self._ci[1]]
        if self.four_screen:
            self.nt = list(self._ci)
            self._mirroring = "four-screen"
        else:
            self.mirroring = h.mirroring
        self.set_prg32(0)
        self.set_chr8(0)
        if rom.trainer:
            self.prg_ram[0x1000:0x1200] = rom.trainer

    # -- nametable mapping ---------------------------------------------------
    @property
    def mirroring(self):
        return self._mirroring

    @mirroring.setter
    def mirroring(self, mode):
        if self.four_screen:
            return
        ci = self._ci
        if mode == "horizontal":
            self.nt = [ci[0], ci[0], ci[1], ci[1]]
        elif mode == "vertical":
            self.nt = [ci[0], ci[1], ci[0], ci[1]]
        elif mode == "one-screen-lo":
            self.nt = [ci[0]] * 4
        elif mode == "one-screen-hi":
            self.nt = [ci[1]] * 4
        else:
            return
        self._mirroring = mode

    def mirror4(self, v):
        self.mirroring = _MIRROR4[v & 3]

    def mirror_vh(self, horizontal):
        self.mirroring = "horizontal" if horizontal else "vertical"

    def chr_page_copy(self, bank):
        off = (bank % self.chr_count1) << 10
        return bytearray(self.chr[off:off + 1024])

    def ensure_chr_ram(self, size):
        if self.rom.has_chr_ram and len(self.chr) < size:
            self.chr.extend(bytes(size - len(self.chr)))
            self.chr_count1 = len(self.chr) >> 10

    # -- banking helpers (negative bank = counted from the end) ---------------
    def set_prg8(self, slot, bank):
        self.prg_map[slot] = (bank % self.prg_count8) << 13

    def set_prg16(self, slot, bank):
        b = bank * 2
        self.set_prg8(slot * 2, b)
        self.set_prg8(slot * 2 + 1, b + 1)

    def set_prg32(self, bank):
        b = bank * 4
        for i in range(4):
            self.set_prg8(i, b + i)

    def set_chr1(self, slot, bank):
        self.chr_map[slot] = (bank % self.chr_count1) << 10

    def set_chr2(self, slot, bank):
        self.set_chr1(slot * 2, bank * 2)
        self.set_chr1(slot * 2 + 1, bank * 2 + 1)

    def set_chr4(self, slot, bank):
        for i in range(4):
            self.set_chr1(slot * 4 + i, bank * 4 + i)

    def set_chr8(self, bank):
        for i in range(8):
            self.set_chr1(i, bank * 8 + i)

    # -- bus -----------------------------------------------------------------
    def cpu_read(self, addr):
        if addr >= 0x8000:
            return self.prg[self.prg_map[(addr >> 13) & 3] | (addr & 0x1FFF)]
        if addr >= 0x6000:
            if self.prg_ram_enabled:
                return self.prg_ram[addr & 0x1FFF]
            return addr >> 8
        return self.read_low(addr)

    def cpu_write(self, addr, val):
        if addr >= 0x8000:
            self.write_reg(addr, val)
        elif addr >= 0x6000:
            if self.prg_ram_enabled and self.prg_ram_writable:
                self.prg_ram[addr & 0x1FFF] = val
        else:
            self.write_low(addr, val)

    def read_low(self, addr):
        return addr >> 8

    def write_low(self, addr, val):
        pass

    def write_reg(self, addr, val):
        pass

    def ppu_read(self, addr):
        return self.chr[self.chr_map[addr >> 10] | (addr & 0x3FF)]

    def ppu_write(self, addr, val):
        if self.chr_writable:
            self.chr[self.chr_map[addr >> 10] | (addr & 0x3FF)] = val

    # -- timing hooks ----------------------------------------------------------
    def on_scanline(self, line, rendering):
        if rendering and (line < 240 or line == 261):
            self.scanline_tick()

    def scanline_tick(self):
        pass

    def a12_rise(self):
        pass

    def cpu_clock(self, cycles):
        pass

    def set_fetch(self, phase, large):
        pass

    def audio_clock(self, cycles):
        pass

    def audio_output(self):
        return 0.0

    # -- battery -----------------------------------------------------------------
    def battery_data(self):
        return bytes(self.prg_ram)

    def load_battery(self, data):
        n = min(len(data), len(self.prg_ram))
        self.prg_ram[:n] = data[:n]


class NROM(Mapper):
    pass


class MMC1(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        h = rom.header
        self.ram_banked = h.is_nes2 and (h.prg_ram + h.prg_nvram) > 8192
        self.prg_512 = len(self.prg) >= 0x80000
        self.shift = 0x10
        self.control = 0x0C
        self.chr0 = 0
        self.chr1 = 0
        self.prg_bank = 0
        self.last_write = -1
        self.ram_off = 0
        self._update()

    def _update(self):
        c = self.control
        self.mirroring = ("one-screen-lo", "one-screen-hi",
                          "vertical", "horizontal")[c & 3]
        if c & 0x10:
            self.set_chr4(0, self.chr0)
            self.set_chr4(1, self.chr1)
        else:
            self.set_chr4(0, self.chr0 & 0x1E)
            self.set_chr4(1, (self.chr0 & 0x1E) | 1)
        outer = (self.chr0 & 0x10) if self.prg_512 else 0
        bank = self.prg_bank & 0x0F
        mode = (c >> 2) & 3
        if mode < 2:
            self.set_prg16(0, outer | (bank & 0x0E))
            self.set_prg16(1, outer | (bank & 0x0E) | 1)
        elif mode == 2:
            self.set_prg16(0, outer)
            self.set_prg16(1, outer | bank)
        else:
            self.set_prg16(0, outer | bank)
            self.set_prg16(1, outer | 0x0F)
        self.prg_ram_enabled = not (self.prg_bank & 0x10)
        if self.ram_banked:
            self.ram_off = (((self.chr0 >> 2) & 3) << 13) % len(self.prg_ram)

    def cpu_read(self, addr):
        if addr >= 0x8000:
            return self.prg[self.prg_map[(addr >> 13) & 3] | (addr & 0x1FFF)]
        if addr >= 0x6000 and self.prg_ram_enabled:
            return self.prg_ram[self.ram_off | (addr & 0x1FFF)]
        return addr >> 8

    def cpu_write(self, addr, val):
        if addr >= 0x8000:
            self.write_reg(addr, val)
        elif addr >= 0x6000 and self.prg_ram_enabled:
            self.prg_ram[self.ram_off | (addr & 0x1FFF)] = val

    def write_reg(self, addr, val):
        # The serial port ignores the second write of a read-modify-write.
        if self.cpu is not None:
            cyc = self.cpu.cycles
            if cyc == self.last_write:
                return
            self.last_write = cyc
        if val & 0x80:
            self.shift = 0x10
            self.control |= 0x0C
            self._update()
            return
        done = self.shift & 1
        self.shift = (self.shift >> 1) | ((val & 1) << 4)
        if done:
            v = self.shift
            self.shift = 0x10
            reg = (addr >> 13) & 3
            if reg == 0:
                self.control = v
            elif reg == 1:
                self.chr0 = v
            elif reg == 2:
                self.chr1 = v
            else:
                self.prg_bank = v
            self._update()


class UxROM(Mapper):
    shift = 0

    def __init__(self, rom):
        super().__init__(rom)
        self.set_prg16(0, 0)
        self.set_prg16(1, -1)

    def write_reg(self, addr, val):
        self.set_prg16(0, val >> self.shift)


class UN1ROM(UxROM):
    shift = 2


class UNROM180(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        self.set_prg16(0, 0)
        self.set_prg16(1, 0)

    def write_reg(self, addr, val):
        self.set_prg16(1, val & 7)


class CNROM(Mapper):
    def write_reg(self, addr, val):
        self.set_chr8(val)


class CNROM185(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        self.chr_on = True

    def write_reg(self, addr, val):
        self.chr_on = bool(val & 3) and val != 0x13

    def ppu_read(self, addr):
        if not self.chr_on:
            return 0xFF
        return self.chr[self.chr_map[addr >> 10] | (addr & 0x3FF)]


class AxROM(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        self.mirroring = "one-screen-lo"

    def write_reg(self, addr, val):
        self.set_prg32(val & 0x0F)
        self.mirroring = "one-screen-hi" if (val & 0x10) else "one-screen-lo"


class MMC2(Mapper):
    mmc4 = False

    def __init__(self, rom):
        super().__init__(rom)
        self.chr_regs = [0, 0, 0, 0]
        self.latch0 = 1
        self.latch1 = 1
        if self.mmc4:
            self.set_prg16(0, 0)
            self.set_prg16(1, -1)
        else:
            self.set_prg8(0, 0)
            self.set_prg8(1, -3)
            self.set_prg8(2, -2)
            self.set_prg8(3, -1)
        self._update_chr()

    def _update_chr(self):
        self.set_chr4(0, self.chr_regs[self.latch0])
        self.set_chr4(1, self.chr_regs[2 + self.latch1])

    def write_reg(self, addr, val):
        r = addr & 0xF000
        if r == 0xA000:
            if self.mmc4:
                self.set_prg16(0, val & 0x0F)
            else:
                self.set_prg8(0, val & 0x0F)
        elif 0xB000 <= r <= 0xE000:
            self.chr_regs[(r - 0xB000) >> 12] = val & 0x1F
            self._update_chr()
        elif r == 0xF000:
            self.mirror_vh(val & 1)

    def ppu_read(self, addr):
        v = self.chr[self.chr_map[addr >> 10] | (addr & 0x3FF)]
        low = addr & 0x0FFF
        if 0x0FD8 <= low <= 0x0FEF:
            if (addr & 0x1000) or self.mmc4:
                if low <= 0x0FDF:
                    new = 0
                elif low >= 0x0FE8:
                    new = 1
                else:
                    return v
            elif low == 0x0FD8:
                new = 0
            elif low == 0x0FE8:
                new = 1
            else:
                return v
            if addr & 0x1000:
                if new != self.latch1:
                    self.latch1 = new
                    self._update_chr()
            elif new != self.latch0:
                self.latch0 = new
                self._update_chr()
        return v


class MMC4(MMC2):
    mmc4 = True


class ColorDreams(Mapper):
    def write_reg(self, addr, val):
        self.set_prg32(val & 3)
        self.set_chr8(val >> 4)


class CPROM(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        self.ensure_chr_ram(16384)
        self.set_chr4(0, 0)
        self.set_chr4(1, 0)

    def write_reg(self, addr, val):
        self.set_chr4(1, val & 3)


class GxROM(Mapper):
    def write_reg(self, addr, val):
        self.set_prg32((val >> 4) & 3)
        self.set_chr8(val & 3)


class Mapper34(Mapper):
    """BNROM ($8000 latch) or NINA-001 ($7FFD-$7FFF) by CHR size."""

    def __init__(self, rom):
        super().__init__(rom)
        self.nina = (not rom.has_chr_ram) and len(self.chr) > 8192

    def cpu_write(self, addr, val):
        super().cpu_write(addr, val)
        if self.nina and 0x7FFD <= addr <= 0x7FFF:
            if addr == 0x7FFD:
                self.set_prg32(val & 1)
            elif addr == 0x7FFE:
                self.set_chr4(0, val & 0x0F)
            else:
                self.set_chr4(1, val & 0x0F)

    def write_reg(self, addr, val):
        if not self.nina:
            self.set_prg32(val)


class Bandai74161(Mapper):
    single = False

    def __init__(self, rom):
        super().__init__(rom)
        self.set_prg16(1, -1)

    def write_reg(self, addr, val):
        self.set_prg16(0, (val >> 4) & (7 if self.single else 0x0F))
        self.set_chr8(val & 0x0F)
        if self.single:
            self.mirroring = "one-screen-hi" if (val & 0x80) else "one-screen-lo"


class Bandai152(Bandai74161):
    single = True


class Camerica(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        self.set_prg16(1, -1)

    def write_reg(self, addr, val):
        if 0x9000 <= addr < 0xA000:
            self.mirroring = "one-screen-hi" if (val & 0x10) else "one-screen-lo"
        elif addr >= 0xC000:
            self.set_prg16(0, val)


class Camerica232(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        self.outer = 0
        self.inner = 0
        self._update()

    def _update(self):
        self.set_prg16(0, (self.outer << 2) | self.inner)
        self.set_prg16(1, (self.outer << 2) | 3)

    def write_reg(self, addr, val):
        if addr < 0xC000:
            self.outer = (val >> 3) & 3
        else:
            self.inner = val & 3
        self._update()


class JalecoJF17(Mapper):
    high = False

    def __init__(self, rom):
        super().__init__(rom)
        self.set_prg16(0, 0)
        self.set_prg16(1, -1)

    def write_reg(self, addr, val):
        if val & 0x80:
            self.set_prg16(1 if self.high else 0, val & 0x0F)
        if val & 0x40:
            self.set_chr8(val & 0x0F)


class JalecoJF19(JalecoJF17):
    high = True


class Irem77(Mapper):
    """Napoleon Senki: 2K CHR-ROM window + 6K CHR-RAM + four-screen RAM."""

    def __init__(self, rom):
        super().__init__(rom)
        self.four_screen = True
        self.nt = list(self._ci)
        self._mirroring = "four-screen"
        self.chr_ram = bytearray(8192)
        self.chr_bank = 0

    def write_reg(self, addr, val):
        self.set_prg32(val & 0x0F)
        self.chr_bank = val >> 4

    def ppu_read(self, addr):
        if addr < 0x0800:
            n = max(1, len(self.chr) >> 11)
            return self.chr[((self.chr_bank % n) << 11) | addr]
        return self.chr_ram[addr]

    def ppu_write(self, addr, val):
        if addr >= 0x0800:
            self.chr_ram[addr] = val


class Irem78(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        h = rom.header
        self.hv = h.submapper == 3 or h.four_screen
        if h.four_screen:
            self.four_screen = False
            self.mirroring = "horizontal"
        self.set_prg16(1, -1)

    def write_reg(self, addr, val):
        self.set_prg16(0, val & 7)
        self.set_chr8(val >> 4)
        if self.hv:
            self.mirror_vh(not (val & 8))
        else:
            self.mirroring = "one-screen-hi" if (val & 8) else "one-screen-lo"


class NINA0306(Mapper):
    def write_low(self, addr, val):
        if (addr & 0xE100) == 0x4100:
            self.set_prg32((val >> 3) & 1)
            self.set_chr8(val & 7)


class NINA113(Mapper):
    def write_low(self, addr, val):
        if (addr & 0xE100) == 0x4100:
            self.set_prg32((val >> 3) & 7)
            self.set_chr8((val & 7) | ((val >> 3) & 8))
            self.mirror_vh(not (val & 0x80))


class Sunsoft89(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        self.set_prg16(1, -1)

    def write_reg(self, addr, val):
        self.set_prg16(0, (val >> 4) & 7)
        self.set_chr8((val & 7) | ((val >> 4) & 8))
        self.mirroring = "one-screen-hi" if (val & 8) else "one-screen-lo"


class Sunsoft93(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        self.set_prg16(1, -1)

    def write_reg(self, addr, val):
        self.set_prg16(0, (val >> 4) & 7)
        if self.rom.has_chr_ram:
            self.chr_writable = bool(val & 1)


class IremTAMS1(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        self.set_prg16(0, -1)
        self.set_prg16(1, 0)

    def write_reg(self, addr, val):
        self.set_prg16(1, val & 0x1F)
        self.mirroring = ("one-screen-lo", "horizontal",
                          "vertical", "one-screen-hi")[val >> 6]


class _Latch6000(Mapper):
    """Discrete boards whose only register lives in $6000-$7FFF."""

    def cpu_write(self, addr, val):
        if 0x6000 <= addr < 0x8000:
            self.latch(addr, val)
        elif addr < 0x6000:
            self.write_low(addr, val)

    def cpu_read(self, addr):
        if addr >= 0x8000:
            return self.prg[self.prg_map[(addr >> 13) & 3] | (addr & 0x1FFF)]
        return addr >> 8

    def latch(self, addr, val):
        pass


class JalecoJF13(_Latch6000):
    def latch(self, addr, val):
        if addr < 0x7000:
            self.set_prg32((val >> 4) & 3)
            self.set_chr8((val & 3) | ((val >> 4) & 4))


class Jaleco87(_Latch6000):
    def latch(self, addr, val):
        self.set_chr8(((val & 1) << 1) | ((val >> 1) & 1))


class Jaleco140(_Latch6000):
    def latch(self, addr, val):
        self.set_prg32((val >> 4) & 3)
        self.set_chr8(val & 0x0F)


class Sunsoft1(_Latch6000):
    def latch(self, addr, val):
        self.set_chr4(0, val & 7)
        self.set_chr4(1, (val >> 4) & 7)


class VRC1(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        self.chr_regs = [0, 0]
        self.set_prg8(3, -1)
        self._update()

    def _update(self):
        self.set_chr4(0, self.chr_regs[0])
        self.set_chr4(1, self.chr_regs[1])

    def write_reg(self, addr, val):
        r = addr & 0xF000
        if r == 0x8000:
            self.set_prg8(0, val & 0x0F)
        elif r == 0x9000:
            self.mirror_vh(val & 1)
            self.chr_regs[0] = (self.chr_regs[0] & 0x0F) | ((val << 3) & 0x10)
            self.chr_regs[1] = (self.chr_regs[1] & 0x0F) | ((val << 2) & 0x10)
            self._update()
        elif r == 0xA000:
            self.set_prg8(1, val & 0x0F)
        elif r == 0xC000:
            self.set_prg8(2, val & 0x0F)
        elif r == 0xE000:
            self.chr_regs[0] = (self.chr_regs[0] & 0x10) | (val & 0x0F)
            self._update()
        elif r == 0xF000:
            self.chr_regs[1] = (self.chr_regs[1] & 0x10) | (val & 0x0F)
            self._update()


# --- MMC3 family -------------------------------------------------------------

class MMC3(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        self.bank_select = 0
        self.regs = [0, 2, 4, 5, 6, 7, 0, 1]
        self.irq_latch = 0
        self.irq_counter = 0
        self.irq_reload = False
        self.irq_enable = False
        self._update()

    def _prg_bank(self, b):
        return b

    def _chr_bank(self, b):
        return b

    def _update(self):
        self._update_prg()
        self._update_chr()

    def _update_prg(self):
        r = self.regs
        pb = self._prg_bank
        if self.bank_select & 0x40:
            self.set_prg8(0, pb(-2))
            self.set_prg8(2, pb(r[6]))
        else:
            self.set_prg8(0, pb(r[6]))
            self.set_prg8(2, pb(-2))
        self.set_prg8(1, pb(r[7]))
        self.set_prg8(3, pb(-1))

    def _chr_banks(self):
        r = self.regs
        return (r[0] & 0xFE, r[0] | 1, r[1] & 0xFE, r[1] | 1,
                r[2], r[3], r[4], r[5])

    def _update_chr(self):
        inv = 4 if (self.bank_select & 0x80) else 0
        cb = self._chr_bank
        for i, b in enumerate(self._chr_banks()):
            self.set_chr1(i ^ inv, cb(b))

    def write_reg(self, addr, val):
        odd = addr & 1
        if addr < 0xA000:
            if odd:
                self.regs[self.bank_select & 7] = val
            else:
                self.bank_select = val
            self._update()
        elif addr < 0xC000:
            if not odd:
                self.mirror_vh(val & 1)
        elif addr < 0xE000:
            if odd:
                self.irq_reload = True
                self.irq_counter = 0
            else:
                self.irq_latch = val
        else:
            self.irq_enable = bool(odd)
            if not odd:
                self.irq_pending = False

    def scanline_tick(self):
        if self.irq_counter == 0 or self.irq_reload:
            self.irq_counter = self.irq_latch
            self.irq_reload = False
        else:
            self.irq_counter -= 1
        if self.irq_counter == 0 and self.irq_enable:
            self.irq_pending = True

    def a12_rise(self):
        self.scanline_tick()


class TxSROM(MMC3):
    """Mapper 118: CHR bank bit 7 drives CIRAM A10."""

    def _update_chr(self):
        super()._update_chr()
        r = self.regs
        if self.bank_select & 0x80:
            nts = (r[2], r[3], r[4], r[5])
        else:
            nts = (r[0], r[0], r[1], r[1])
        self.nt = [self._ci[(b >> 7) & 1] for b in nts]

    def write_reg(self, addr, val):
        if 0xA000 <= addr < 0xC000 and not (addr & 1):
            return
        super().write_reg(addr, val)


class TQROM(MMC3):
    """Mapper 119: CHR bank bit 6 selects 8K CHR-RAM instead of CHR-ROM."""

    def __init__(self, rom):
        self.chr_ram = bytearray(8192)
        self.chr_srcs = [rom.chr] * 8
        super().__init__(rom)

    def _update_chr(self):
        inv = 4 if (self.bank_select & 0x80) else 0
        for i, b in enumerate(self._chr_banks()):
            slot = i ^ inv
            if b & 0x40:
                self.chr_srcs[slot] = self.chr_ram
                self.chr_map[slot] = (b & 7) << 10
            else:
                self.chr_srcs[slot] = self.chr
                self.chr_map[slot] = (b % self.chr_count1) << 10

    def ppu_read(self, addr):
        s = addr >> 10
        return self.chr_srcs[s][self.chr_map[s] | (addr & 0x3FF)]

    def ppu_write(self, addr, val):
        s = addr >> 10
        if self.chr_srcs[s] is self.chr_ram:
            self.chr_ram[self.chr_map[s] | (addr & 0x3FF)] = val


class MMC3Multi47(MMC3):
    """Super Spike V'Ball + Nintendo World Cup."""

    def __init__(self, rom):
        self.block = 0
        super().__init__(rom)

    def _prg_bank(self, b):
        return (b & 0x0F) | (self.block << 4)

    def _chr_bank(self, b):
        return (b & 0x7F) | (self.block << 7)

    def cpu_write(self, addr, val):
        if 0x6000 <= addr < 0x8000:
            self.block = val & 1
            self._update()
        else:
            super().cpu_write(addr, val)


class MMC3Multi37(MMC3Multi47):
    """Super Mario Bros. + Tetris + Nintendo World Cup."""

    def _prg_bank(self, b):
        blk = self.block
        if blk <= 2:
            return b & 7
        if blk == 3:
            return (b & 7) | 0x08
        if blk == 7:
            return (b & 7) | 0x18
        return (b & 0x0F) | 0x10

    def _chr_bank(self, b):
        return (b & 0x7F) | ((self.block & 4) << 5)

    def cpu_write(self, addr, val):
        if 0x6000 <= addr < 0x8000:
            self.block = val & 7
            self._update()
        else:
            MMC3.cpu_write(self, addr, val)


class Namco108(MMC3):
    """Mapper 206 (DxROM / Namco 108): MMC3 subset, no IRQ, fixed mirroring."""

    def write_reg(self, addr, val):
        if addr < 0xA000:
            if addr & 1:
                self.regs[self.bank_select & 7] = val & 0x3F
            else:
                self.bank_select = val & 7
            self._update()

    def scanline_tick(self):
        pass


class Namco3446(Namco108):
    def _update_chr(self):
        r = self.regs
        for i in range(4):
            self.set_chr2(i, r[2 + i])


class Namco88(Namco108):
    def _update_chr(self):
        r = self.regs
        self.set_chr1(0, r[0] & 0x3E)
        self.set_chr1(1, (r[0] & 0x3E) | 1)
        self.set_chr1(2, r[1] & 0x3E)
        self.set_chr1(3, (r[1] & 0x3E) | 1)
        for i in range(4):
            self.set_chr1(4 + i, r[2 + i] | 0x40)


class Namco154(Namco88):
    def write_reg(self, addr, val):
        self.mirroring = "one-screen-hi" if (val & 0x40) else "one-screen-lo"
        super().write_reg(addr, val)


class Namco3425(Namco108):
    def _update_chr(self):
        super()._update_chr()
        r = self.regs
        a = self._ci[(r[0] >> 5) & 1]
        b = self._ci[(r[1] >> 5) & 1]
        self.nt = [a, a, b, b]


class RAMBO1(Mapper):
    """Mapper 64 (Tengen RAMBO-1)."""
    needs_cpu_clock = True

    def __init__(self, rom):
        super().__init__(rom)
        self.bank_select = 0
        self.regs = [0] * 16
        self.irq_latch = 0
        self.irq_counter = 0
        self.irq_reload = False
        self.irq_enable = False
        self.cycle_mode = False
        self.prescaler = 0
        self._update()

    def _update(self):
        r = self.regs
        inv = 4 if (self.bank_select & 0x80) else 0
        if self.bank_select & 0x20:
            banks = (r[0], r[8], r[1], r[9], r[2], r[3], r[4], r[5])
        else:
            banks = (r[0] & 0xFE, r[0] | 1, r[1] & 0xFE, r[1] | 1,
                     r[2], r[3], r[4], r[5])
        for i, b in enumerate(banks):
            self.set_chr1(i ^ inv, b)
        if self.bank_select & 0x40:
            self.set_prg8(0, r[15])
            self.set_prg8(1, r[6])
            self.set_prg8(2, r[7])
        else:
            self.set_prg8(0, r[6])
            self.set_prg8(1, r[7])
            self.set_prg8(2, r[15])
        self.set_prg8(3, -1)

    def write_reg(self, addr, val):
        odd = addr & 1
        if addr < 0xA000:
            if odd:
                self.regs[self.bank_select & 0x0F] = val
            else:
                self.bank_select = val
            self._update()
        elif addr < 0xC000:
            if not odd:
                self.mirror_vh(val & 1)
        elif addr < 0xE000:
            if odd:
                self.cycle_mode = bool(val & 1)
                self.irq_reload = True
                self.prescaler = 0
            else:
                self.irq_latch = val
        else:
            self.irq_enable = bool(odd)
            if not odd:
                self.irq_pending = False

    def _tick(self):
        if self.irq_reload:
            self.irq_counter = self.irq_latch + (1 if self.irq_latch else 0)
            self.irq_reload = False
        elif self.irq_counter == 0:
            self.irq_counter = self.irq_latch
        else:
            self.irq_counter -= 1
        if self.irq_counter == 0 and self.irq_enable:
            self.irq_pending = True

    def scanline_tick(self):
        if not self.cycle_mode:
            self._tick()

    def cpu_clock(self, cycles):
        if self.cycle_mode:
            self.prescaler += cycles
            while self.prescaler >= 4:
                self.prescaler -= 4
                self._tick()


# --- MMC5 --------------------------------------------------------------------

class MMC5(Mapper):
    split_chr = True
    has_audio = True

    def __init__(self, rom):
        super().__init__(rom)
        if len(self.prg_ram) < 65536:
            self.prg_ram = bytearray(65536)
        self.ram_count8 = len(self.prg_ram) >> 13
        self.exram = bytearray(1024)
        self._exram_page = memoryview(self.exram)
        self._zero_page = bytearray(1024)
        self._fill = bytearray(1024)
        self.prg_mode = 3
        self.chr_mode = 3
        self.prg_regs = [0, 0, 0, 0, 0xFF]
        self.chr_a = [0] * 8
        self.chr_b = [0] * 4
        self.chr_hi = 0
        self.last_b = False
        self.exram_mode = 0
        self.nt_ctrl = 0
        self.fill_tile = 0
        self.fill_attr = 0
        self.ram_protect = [0, 0]
        self.irq_target = 0
        self.irq_enabled = False
        self.irq_flag = False
        self.in_frame = False
        self.line_counter = 0
        self.mul_a = 0xFF
        self.mul_b = 0xFF
        self.slots = [(True, 0)] * 5
        self.chr_map_a = [0] * 8
        self.chr_map_b = [0] * 8
        self.large = False
        self.fetch = 2
        self.pulses = (_Pulse(1), _Pulse(1))
        self.pcm = 0
        self.frame_acc = 0
        self._update_prg()
        self._update_chr()
        self._update_fill()
        self._update_nt()

    def _sel(self, v, b, rom=False):
        if rom or (v & 0x80):
            return (False, (b % self.prg_count8) << 13)
        return (True, (b % self.ram_count8) << 13)

    def _update_prg(self):
        r = self.prg_regs
        m = self.prg_mode
        s = [None] * 5
        s[0] = (True, ((r[0] & 7) % self.ram_count8) << 13)
        if m == 0:
            b = r[4] & 0x7C
            for i in range(4):
                s[1 + i] = self._sel(0x80, b + i)
        elif m == 1:
            b = r[2] & 0x7E
            s[1] = self._sel(r[2], b)
            s[2] = self._sel(r[2], b + 1)
            b = r[4] & 0x7E
            s[3] = self._sel(0x80, b)
            s[4] = self._sel(0x80, b + 1)
        elif m == 2:
            b = r[2] & 0x7E
            s[1] = self._sel(r[2], b)
            s[2] = self._sel(r[2], b + 1)
            s[3] = self._sel(r[3], r[3] & 0x7F)
            s[4] = self._sel(0x80, r[4] & 0x7F)
        else:
            for i in range(1, 4):
                s[i] = self._sel(r[i], r[i] & 0x7F)
            s[4] = self._sel(0x80, r[4] & 0x7F)
        self.slots = s
        self.slot_buf = [self.prg_ram if ram else self.prg for ram, _ in s]
        self.slot_off = [off for _, off in s]

    def _update_chr(self):
        a, b, m = self.chr_a, self.chr_b, self.chr_mode
        cnt = self.chr_count1

        def off(bank):
            return (bank % cnt) << 10

        if m == 0:
            ma = [off(a[7] * 8 + i) for i in range(8)]
            mb = [off(b[3] * 8 + i) for i in range(8)]
        elif m == 1:
            ma = [off(a[3] * 4 + i) for i in range(4)] + \
                 [off(a[7] * 4 + i) for i in range(4)]
            mb = [off(b[3] * 4 + i) for i in range(4)] * 2
        elif m == 2:
            ma = []
            for r in (a[1], a[3], a[5], a[7]):
                ma += [off(r * 2), off(r * 2 + 1)]
            mb = [off(b[1] * 2), off(b[1] * 2 + 1),
                  off(b[3] * 2), off(b[3] * 2 + 1)] * 2
        else:
            ma = [off(x) for x in a]
            mb = [off(x) for x in b] * 2
        self.chr_map_a = ma
        self.chr_map_b = mb
        self.set_fetch(self.fetch, self.large)

    def set_fetch(self, phase, large):
        self.large = bool(large)
        self.fetch = phase
        if large and phase == 0:
            self.chr_map = self.chr_map_b
        elif large and phase == 1:
            self.chr_map = self.chr_map_a
        else:
            self.chr_map = self.chr_map_b if self.last_b else self.chr_map_a

    def _update_fill(self):
        a = self.fill_attr & 3
        self._fill[0:960] = bytes((self.fill_tile,)) * 960
        self._fill[960:1024] = bytes((a | (a << 2) | (a << 4) | (a << 6),)) * 64

    def _update_nt(self):
        pages = []
        for i in range(4):
            s = (self.nt_ctrl >> (i * 2)) & 3
            if s < 2:
                pages.append(self._ci[s])
            elif s == 2:
                pages.append(self._exram_page if self.exram_mode < 2
                             else self._zero_page)
            else:
                pages.append(self._fill)
        self.nt = pages

    def ext_attr(self, nt_off, tile, fine_y):
        e = self.exram[nt_off]
        bank = (e & 0x3F) | (self.chr_hi << 6)
        n = len(self.chr)
        a = ((bank << 12) | (tile << 4) | fine_y) % n
        return self.chr[a], self.chr[(a + 8) % n], e >> 6

    def cpu_read(self, addr):
        if addr >= 0x6000:
            i = (addr >> 13) - 3
            return self.slot_buf[i][self.slot_off[i] | (addr & 0x1FFF)]
        if addr >= 0x5C00:
            if self.exram_mode >= 2:
                return self.exram[addr - 0x5C00]
            return addr >> 8
        if addr == 0x5204:
            v = (0x80 if self.irq_flag else 0) | (0x40 if self.in_frame else 0)
            self.irq_flag = False
            self.irq_pending = False
            return v
        if addr == 0x5205:
            return (self.mul_a * self.mul_b) & 0xFF
        if addr == 0x5206:
            return (self.mul_a * self.mul_b) >> 8
        if addr == 0x5015:
            p0, p1 = self.pulses
            return (1 if p0.length_counter else 0) | (2 if p1.length_counter else 0)
        return addr >> 8

    def cpu_write(self, addr, val):
        if addr >= 0x6000:
            is_ram, off = self.slots[(addr >> 13) - 3]
            if is_ram and self.ram_protect[0] == 2 and self.ram_protect[1] == 1:
                self.prg_ram[off | (addr & 0x1FFF)] = val
            return
        if addr >= 0x5C00:
            if self.exram_mode != 3:
                self.exram[addr - 0x5C00] = val
            return
        if addr < 0x5100:
            self._audio_write(addr, val)
            return
        if addr == 0x5100:
            self.prg_mode = val & 3
            self._update_prg()
        elif addr == 0x5101:
            self.chr_mode = val & 3
            self._update_chr()
        elif addr == 0x5102:
            self.ram_protect[0] = val & 3
        elif addr == 0x5103:
            self.ram_protect[1] = val & 3
        elif addr == 0x5104:
            self.exram_mode = val & 3
            self._update_nt()
        elif addr == 0x5105:
            self.nt_ctrl = val
            self._update_nt()
        elif addr == 0x5106:
            self.fill_tile = val
            self._update_fill()
        elif addr == 0x5107:
            self.fill_attr = val & 3
            self._update_fill()
        elif 0x5113 <= addr <= 0x5117:
            self.prg_regs[addr - 0x5113] = val
            self._update_prg()
        elif 0x5120 <= addr <= 0x5127:
            self.chr_a[addr - 0x5120] = val | (self.chr_hi << 8)
            self.last_b = False
            self._update_chr()
        elif 0x5128 <= addr <= 0x512B:
            self.chr_b[addr - 0x5128] = val | (self.chr_hi << 8)
            self.last_b = True
            self._update_chr()
        elif addr == 0x5130:
            self.chr_hi = val & 3
        elif addr == 0x5203:
            self.irq_target = val
        elif addr == 0x5204:
            self.irq_enabled = bool(val & 0x80)
            self.irq_pending = self.irq_flag and self.irq_enabled
        elif addr == 0x5205:
            self.mul_a = val
        elif addr == 0x5206:
            self.mul_b = val

    def _audio_write(self, addr, val):
        if addr <= 0x5007:
            p = self.pulses[(addr >> 2) & 1]
            r = addr & 3
            if r == 0:
                p.write_reg0(val)
            elif r == 2:
                p.write_reg2(val)
            elif r == 3:
                p.write_reg3(val)
        elif addr == 0x5011:
            if val:
                self.pcm = val
        elif addr == 0x5015:
            for i, p in enumerate(self.pulses):
                p.enabled = bool(val & (1 << i))
                if not p.enabled:
                    p.length_counter = 0

    def on_scanline(self, line, rendering):
        if line < 240 and rendering:
            if not self.in_frame:
                self.in_frame = True
                self.line_counter = 0
                self.irq_flag = False
            else:
                self.line_counter += 1
            if self.irq_target and self.line_counter == self.irq_target:
                self.irq_flag = True
            self.irq_pending = self.irq_flag and self.irq_enabled
        else:
            self.in_frame = False

    def audio_clock(self, cycles):
        p0, p1 = self.pulses
        if p0.enabled:
            p0.clock_timer(cycles)
        if p1.enabled:
            p1.clock_timer(cycles)
        self.frame_acc += cycles
        while self.frame_acc >= 7457:
            self.frame_acc -= 7457
            for p in self.pulses:
                p.clock_envelope()
                p.clock_length()

    def audio_output(self):
        p0, p1 = self.pulses
        return (p0.output() + p1.output()) * 0.0086 + self.pcm * 0.0004


# --- Konami VRC family -------------------------------------------------------

class _VrcIrqMixin:
    def _irq_init(self):
        self.irq_latch = 0
        self.irq_counter = 0
        self.irq_enabled = False
        self.irq_enable_after = False
        self.irq_cycle_mode = False
        self.irq_prescaler = 341

    def _irq_control(self, val):
        self.irq_enable_after = bool(val & 1)
        self.irq_enabled = bool(val & 2)
        self.irq_cycle_mode = bool(val & 4)
        if self.irq_enabled:
            self.irq_counter = self.irq_latch
            self.irq_prescaler = 341
        self.irq_pending = False

    def _irq_ack(self):
        self.irq_pending = False
        self.irq_enabled = self.irq_enable_after

    def cpu_clock(self, cycles):
        if not self.irq_enabled:
            return
        if self.irq_cycle_mode:
            ticks = cycles
        else:
            self.irq_prescaler -= cycles * 3
            ticks = 0
            while self.irq_prescaler <= 0:
                self.irq_prescaler += 341
                ticks += 1
            if not ticks:
                return
        c = self.irq_counter + ticks
        if c > 0xFF:
            self.irq_pending = True
            c = self.irq_latch + (c - 0x100) % (0x100 - self.irq_latch)
        self.irq_counter = c


_VRC_PINS = {
    21: ((1, 6), (2, 7)),
    22: ((1,), (0,)),
    23: ((0, 2), (1, 3)),
    25: ((1, 3), (0, 2)),
}


class VRC4(_VrcIrqMixin, Mapper):
    """VRC2 / VRC4 on mappers 21, 22, 23 and 25 (all pin variants OR-ed)."""
    needs_cpu_clock = True

    def __init__(self, rom):
        super().__init__(rom)
        m = rom.header.mapper
        self.pins = _VRC_PINS.get(m, _VRC_PINS[23])
        self.chr_shift = 1 if m == 22 else 0
        self.prg_regs = [0, 0]
        self.prg_swap = False
        self.chr_regs = [0] * 8
        self._irq_init()
        self._update_prg()
        for i in range(8):
            self.set_chr1(i, 0)

    def _update_prg(self):
        if self.prg_swap:
            self.set_prg8(0, -2)
            self.set_prg8(2, self.prg_regs[0])
        else:
            self.set_prg8(0, self.prg_regs[0])
            self.set_prg8(2, -2)
        self.set_prg8(1, self.prg_regs[1])
        self.set_prg8(3, -1)

    def write_reg(self, addr, val):
        p0, p1 = self.pins
        b0 = 0
        for p in p0:
            b0 |= (addr >> p) & 1
        b1 = 0
        for p in p1:
            b1 |= (addr >> p) & 1
        r = (b1 << 1) | b0
        base = addr & 0xF000
        if base == 0x8000:
            self.prg_regs[0] = val & 0x1F
            self._update_prg()
        elif base == 0x9000:
            if r < 2:
                self.mirror4(val)
            elif r == 2:
                self.prg_swap = bool(val & 2)
                self._update_prg()
        elif base == 0xA000:
            self.prg_regs[1] = val & 0x1F
            self._update_prg()
        elif base <= 0xE000:
            idx = ((base - 0xB000) >> 11) | (r >> 1)
            c = self.chr_regs[idx]
            if r & 1:
                c = (c & 0x0F) | ((val & 0x1F) << 4)
            else:
                c = (c & 0x1F0) | (val & 0x0F)
            self.chr_regs[idx] = c
            self.set_chr1(idx, c >> self.chr_shift)
        else:
            if r == 0:
                self.irq_latch = (self.irq_latch & 0xF0) | (val & 0x0F)
            elif r == 1:
                self.irq_latch = (self.irq_latch & 0x0F) | ((val & 0x0F) << 4)
            elif r == 2:
                self._irq_control(val)
            else:
                self._irq_ack()


class _VRC6Pulse:
    __slots__ = ("vol", "duty", "mode", "period", "enabled", "timer", "step")

    def __init__(self):
        self.vol = self.duty = self.mode = self.period = 0
        self.enabled = False
        self.timer = 1
        self.step = 15

    def write(self, r, val):
        if r == 0:
            self.mode = val & 0x80
            self.duty = (val >> 4) & 7
            self.vol = val & 0x0F
        elif r == 1:
            self.period = (self.period & 0xF00) | val
        else:
            self.period = (self.period & 0xFF) | ((val & 0x0F) << 8)
            self.enabled = bool(val & 0x80)
            if not self.enabled:
                self.step = 15

    def clock(self, cycles):
        if not self.enabled:
            return
        t = self.timer - cycles
        if t > 0:
            self.timer = t
            return
        p = self.period + 1
        n = 1 + (-t) // p
        self.timer = t + n * p
        self.step = (self.step - n) & 15

    def output(self):
        if self.enabled and (self.mode or self.step <= self.duty):
            return self.vol
        return 0


class _VRC6Saw:
    __slots__ = ("rate", "period", "enabled", "timer", "sub", "acc")

    def __init__(self):
        self.rate = self.period = self.sub = self.acc = 0
        self.enabled = False
        self.timer = 1

    def write(self, r, val):
        if r == 0:
            self.rate = val & 0x3F
        elif r == 1:
            self.period = (self.period & 0xF00) | val
        else:
            self.period = (self.period & 0xFF) | ((val & 0x0F) << 8)
            self.enabled = bool(val & 0x80)
            if not self.enabled:
                self.acc = 0
                self.sub = 0

    def clock(self, cycles):
        if not self.enabled:
            return
        t = self.timer - cycles
        if t > 0:
            self.timer = t
            return
        p = self.period + 1
        n = 1 + (-t) // p
        self.timer = t + n * p
        for _ in range(n):
            self.sub += 1
            if self.sub == 14:
                self.sub = 0
                self.acc = 0
            elif not (self.sub & 1):
                self.acc = (self.acc + self.rate) & 0xFF

    def output(self):
        return (self.acc >> 3) if self.enabled else 0


class VRC6(_VrcIrqMixin, Mapper):
    needs_cpu_clock = True
    has_audio = True

    def __init__(self, rom):
        super().__init__(rom)
        self.swap = rom.header.mapper == 26
        self._irq_init()
        self.p1 = _VRC6Pulse()
        self.p2 = _VRC6Pulse()
        self.saw = _VRC6Saw()
        self.halt = False
        self.set_prg16(0, 0)
        self.set_prg8(2, 0)
        self.set_prg8(3, -1)
        for i in range(8):
            self.set_chr1(i, i)

    def write_reg(self, addr, val):
        if self.swap:
            addr = (addr & 0xFFFC) | ((addr & 1) << 1) | ((addr >> 1) & 1)
        base = addr & 0xF000
        r = addr & 3
        if base == 0x8000:
            self.set_prg16(0, val & 0x0F)
        elif base == 0x9000:
            if r < 3:
                self.p1.write(r, val)
            else:
                self.halt = bool(val & 1)
        elif base == 0xA000:
            if r < 3:
                self.p2.write(r, val)
        elif base == 0xB000:
            if r < 3:
                self.saw.write(r, val)
            else:
                self.mirror4((val >> 2) & 3)
                self.prg_ram_enabled = bool(val & 0x80)
        elif base == 0xC000:
            self.set_prg8(2, val & 0x1F)
        elif base == 0xD000:
            self.set_chr1(r, val)
        elif base == 0xE000:
            self.set_chr1(4 + r, val)
        else:
            if r == 0:
                self.irq_latch = val
            elif r == 1:
                self._irq_control(val)
            elif r == 2:
                self._irq_ack()

    def audio_clock(self, cycles):
        if self.halt:
            return
        self.p1.clock(cycles)
        self.p2.clock(cycles)
        self.saw.clock(cycles)

    def audio_output(self):
        return (self.p1.output() + self.p2.output() + self.saw.output()) * 0.0068


class VRC7(_VrcIrqMixin, Mapper):
    needs_cpu_clock = True

    def __init__(self, rom):
        super().__init__(rom)
        self._irq_init()
        self.set_prg8(3, -1)

    def write_reg(self, addr, val):
        hi = 1 if (addr & 0x18) else 0
        base = addr & 0xF000
        if base == 0x8000:
            self.set_prg8(hi, val & 0x3F)
        elif base == 0x9000:
            if not hi:
                self.set_prg8(2, val & 0x3F)
        elif base <= 0xD000:
            self.set_chr1(((base - 0xA000) >> 11) | hi, val)
        elif base == 0xE000:
            if hi:
                self.irq_latch = val
            else:
                self.mirror4(val)
                self.prg_ram_enabled = bool(val & 0x80)
        else:
            if hi:
                self._irq_ack()
            else:
                self._irq_control(val)


class VRC3(Mapper):
    needs_cpu_clock = True

    def __init__(self, rom):
        super().__init__(rom)
        self.latch = 0
        self.counter = 0
        self.mode8 = False
        self.enabled = False
        self.enable_after = False
        self.set_prg16(1, -1)

    def write_reg(self, addr, val):
        base = addr & 0xF000
        if base <= 0xB000:
            shift = ((base - 0x8000) >> 12) * 4
            self.latch = (self.latch & ~(0xF << shift)) | ((val & 0x0F) << shift)
        elif base == 0xC000:
            self.enable_after = bool(val & 1)
            self.enabled = bool(val & 2)
            self.mode8 = bool(val & 4)
            if self.enabled:
                self.counter = self.latch
            self.irq_pending = False
        elif base == 0xD000:
            self.irq_pending = False
            self.enabled = self.enable_after
        elif base == 0xF000:
            self.set_prg16(0, val & 7)

    def cpu_clock(self, cycles):
        if not self.enabled:
            return
        if self.mode8:
            lat = self.latch & 0xFF
            lo = (self.counter & 0xFF) + cycles
            if lo > 0xFF:
                self.irq_pending = True
                lo = lat + (lo - 0x100) % (0x100 - lat)
            self.counter = (self.counter & 0xFF00) | lo
        else:
            c = self.counter + cycles
            if c > 0xFFFF:
                self.irq_pending = True
                c = self.latch + (c - 0x10000) % (0x10000 - self.latch)
            self.counter = c


# --- Bandai / Jaleco / Namco / Irem / Taito / Sunsoft ASICs -----------------

class BandaiFCG(Mapper):
    """Mappers 16 / 153 / 159 (FCG-1/2, LZ93D50)."""
    needs_cpu_clock = True

    def __init__(self, rom):
        super().__init__(rom)
        m = rom.header.mapper
        self.mode153 = m == 153
        self.chr_regs = [0] * 8
        self.prg_reg = 0
        self.irq_enabled = False
        self.irq_counter = 0
        self.irq_latch = 0
        self._update()

    def _update(self):
        if self.mode153:
            outer = 0x10 if any(r & 1 for r in self.chr_regs) else 0
            self.set_prg16(0, outer | (self.prg_reg & 0x0F))
            self.set_prg16(1, outer | 0x0F)
        else:
            self.set_prg16(0, self.prg_reg & 0x0F)
            self.set_prg16(1, -1)
            for i in range(8):
                self.set_chr1(i, self.chr_regs[i])

    def _reg(self, addr, val, lz):
        r = addr & 0x0F
        if r < 8:
            self.chr_regs[r] = val
            self._update()
        elif r == 8:
            self.prg_reg = val
            self._update()
        elif r == 9:
            self.mirror4(val)
        elif r == 0x0A:
            self.irq_enabled = bool(val & 1)
            self.irq_pending = False
            if lz:
                self.irq_counter = self.irq_latch
        elif r == 0x0B:
            if lz:
                self.irq_latch = (self.irq_latch & 0xFF00) | val
            else:
                self.irq_counter = (self.irq_counter & 0xFF00) | val
        elif r == 0x0C:
            if lz:
                self.irq_latch = (self.irq_latch & 0x00FF) | (val << 8)
            else:
                self.irq_counter = (self.irq_counter & 0x00FF) | (val << 8)
        elif r == 0x0D and self.mode153:
            self.prg_ram_enabled = bool(val & 0x20)

    def cpu_read(self, addr):
        if 0x6000 <= addr < 0x8000 and not self.mode153:
            return 0x00
        return super().cpu_read(addr)

    def cpu_write(self, addr, val):
        if addr >= 0x8000:
            self._reg(addr, val, True)
        elif addr >= 0x6000:
            if self.mode153:
                if self.prg_ram_enabled:
                    self.prg_ram[addr & 0x1FFF] = val
            else:
                self._reg(addr, val, False)

    def cpu_clock(self, cycles):
        if self.irq_enabled:
            c = self.irq_counter - cycles
            if c <= 0:
                self.irq_pending = True
                c &= 0xFFFF
            self.irq_counter = c


class JalecoSS88006(Mapper):
    needs_cpu_clock = True

    def __init__(self, rom):
        super().__init__(rom)
        self.prg_regs = [0, 0, 0]
        self.chr_regs = [0] * 8
        self.irq_reload = 0
        self.irq_counter = 0
        self.irq_mask = 0xFFFF
        self.irq_enabled = False
        for i in range(3):
            self.set_prg8(i, 0)
        self.set_prg8(3, -1)

    @staticmethod
    def _nib(regs, idx, high, val):
        if high:
            regs[idx] = (regs[idx] & 0x0F) | ((val & 0x0F) << 4)
        else:
            regs[idx] = (regs[idx] & 0xF0) | (val & 0x0F)
        return regs[idx]

    def write_reg(self, addr, val):
        a = addr & 0xF003
        base = a & 0xF000
        if base == 0x8000 or (base == 0x9000 and (a & 3) < 2):
            idx = ((base - 0x8000) >> 11) | ((a & 3) >> 1)
            self.set_prg8(idx, self._nib(self.prg_regs, idx, a & 1, val))
        elif a == 0x9002:
            self.prg_ram_enabled = bool(val & 1)
            self.prg_ram_writable = bool(val & 2)
        elif 0xA000 <= base <= 0xD000:
            idx = ((base - 0xA000) >> 11) | ((a & 3) >> 1)
            self.set_chr1(idx, self._nib(self.chr_regs, idx, a & 1, val))
        elif base == 0xE000:
            shift = (a & 3) * 4
            self.irq_reload = ((self.irq_reload & ~(0xF << shift))
                               | ((val & 0x0F) << shift))
        elif a == 0xF000:
            self.irq_pending = False
            self.irq_counter = self.irq_reload
        elif a == 0xF001:
            self.irq_pending = False
            self.irq_enabled = bool(val & 1)
            self.irq_mask = (0x000F if val & 8 else 0x00FF if val & 4
                             else 0x0FFF if val & 2 else 0xFFFF)
        elif a == 0xF002:
            self.mirroring = ("horizontal", "vertical",
                              "one-screen-lo", "one-screen-hi")[val & 3]

    def cpu_clock(self, cycles):
        if not self.irq_enabled:
            return
        m = self.irq_mask
        c = self.irq_counter & m
        if c > cycles:
            c -= cycles
        else:
            self.irq_pending = True
            c = (c - cycles) & m
        self.irq_counter = (self.irq_counter & ~m) | c


class Namco163(Mapper):
    """Mapper 19 (Namco 129/163) and 210 (Namco 175/340)."""
    needs_cpu_clock = True

    def __init__(self, rom):
        super().__init__(rom)
        h = rom.header
        self.is163 = h.mapper == 19
        self.mirror340 = h.mapper == 210 and h.submapper == 2
        self.chip_ram = bytearray(128)
        self.ram_addr = 0
        self.ram_inc = False
        self.irq_counter = 0
        self.irq_enabled = False
        self.nt_regs = [0xE0, 0xE0, 0xE1, 0xE1]
        for i in range(3):
            self.set_prg8(i, 0)
        self.set_prg8(3, -1)
        if self.is163:
            self.mirroring = h.mirroring

    def _update_nt(self):
        pages = []
        for v in self.nt_regs:
            pages.append(self._ci[v & 1] if v >= 0xE0 else self.chr_page_copy(v))
        self.nt = pages

    def read_low(self, addr):
        if not self.is163:
            return addr >> 8
        if 0x4800 <= addr < 0x5000:
            v = self.chip_ram[self.ram_addr]
            if self.ram_inc:
                self.ram_addr = (self.ram_addr + 1) & 0x7F
            return v
        if 0x5000 <= addr < 0x5800:
            return self.irq_counter & 0xFF
        if 0x5800 <= addr < 0x6000:
            return ((self.irq_counter >> 8) & 0x7F) | (0x80 if self.irq_enabled else 0)
        return addr >> 8

    def write_low(self, addr, val):
        if not self.is163:
            return
        if 0x4800 <= addr < 0x5000:
            self.chip_ram[self.ram_addr] = val
            if self.ram_inc:
                self.ram_addr = (self.ram_addr + 1) & 0x7F
        elif 0x5000 <= addr < 0x5800:
            self.irq_counter = (self.irq_counter & 0x7F00) | val
            self.irq_pending = False
        elif 0x5800 <= addr < 0x6000:
            self.irq_counter = (self.irq_counter & 0x00FF) | ((val & 0x7F) << 8)
            self.irq_enabled = bool(val & 0x80)
            self.irq_pending = False

    def write_reg(self, addr, val):
        r = (addr >> 11) & 0x0F
        if r < 8:
            self.set_chr1(r, val)
        elif r < 12:
            if self.is163:
                self.nt_regs[r - 8] = val
                self._update_nt()
        elif r == 12:
            self.set_prg8(0, val & 0x3F)
            if self.mirror340:
                self.mirroring = ("one-screen-lo", "vertical",
                                  "horizontal", "one-screen-hi")[val >> 6]
        elif r == 13:
            self.set_prg8(1, val & 0x3F)
        elif r == 14:
            self.set_prg8(2, val & 0x3F)
        elif r == 15:
            self.ram_addr = val & 0x7F
            self.ram_inc = bool(val & 0x80)

    def cpu_clock(self, cycles):
        if self.irq_enabled and self.irq_counter < 0x7FFF:
            c = self.irq_counter + cycles
            if c >= 0x7FFF:
                c = 0x7FFF
                self.irq_pending = True
            self.irq_counter = c

    def battery_data(self):
        return bytes(self.prg_ram) + bytes(self.chip_ram)

    def load_battery(self, data):
        n = len(self.prg_ram)
        super().load_battery(data[:n])
        extra = data[n:n + 128]
        self.chip_ram[:len(extra)] = extra


class IremG101(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        self.prg_regs = [0, 0]
        self.mode = 0
        self._update()
        if rom.header.submapper == 1:
            self.mirroring = "one-screen-lo"

    def _update(self):
        if self.mode:
            self.set_prg8(0, -2)
            self.set_prg8(2, self.prg_regs[0])
        else:
            self.set_prg8(0, self.prg_regs[0])
            self.set_prg8(2, -2)
        self.set_prg8(1, self.prg_regs[1])
        self.set_prg8(3, -1)

    def write_reg(self, addr, val):
        base = addr & 0xF000
        if base == 0x8000:
            self.prg_regs[0] = val & 0x1F
            self._update()
        elif base == 0x9000:
            self.mode = (val >> 1) & 1
            if self.header.submapper != 1:
                self.mirror_vh(val & 1)
            self._update()
        elif base == 0xA000:
            self.prg_regs[1] = val & 0x1F
            self._update()
        elif base == 0xB000:
            self.set_chr1(addr & 7, val)


class IremH3001(Mapper):
    needs_cpu_clock = True

    def __init__(self, rom):
        super().__init__(rom)
        self.irq_enabled = False
        self.irq_counter = 0
        self.irq_latch = 0
        for i in range(3):
            self.set_prg8(i, i)
        self.set_prg8(3, -1)

    def write_reg(self, addr, val):
        if addr == 0x8000:
            self.set_prg8(0, val)
        elif addr == 0x9001:
            self.mirror_vh(val & 0x80)
        elif addr == 0x9003:
            self.irq_enabled = bool(val & 0x80)
            self.irq_pending = False
        elif addr == 0x9004:
            self.irq_counter = self.irq_latch
            self.irq_pending = False
        elif addr == 0x9005:
            self.irq_latch = (self.irq_latch & 0x00FF) | (val << 8)
        elif addr == 0x9006:
            self.irq_latch = (self.irq_latch & 0xFF00) | val
        elif addr == 0xA000:
            self.set_prg8(1, val)
        elif 0xB000 <= addr <= 0xB007:
            self.set_chr1(addr & 7, val)
        elif addr == 0xC000:
            self.set_prg8(2, val)

    def cpu_clock(self, cycles):
        if self.irq_enabled and self.irq_counter:
            c = self.irq_counter - cycles
            if c <= 0:
                c = 0
                self.irq_pending = True
            self.irq_counter = c


class TaitoTC0190(Mapper):
    tc0690 = False

    def __init__(self, rom):
        super().__init__(rom)
        self.set_prg8(2, -2)
        self.set_prg8(3, -1)
        self.irq_latch = 0
        self.irq_counter = 0
        self.irq_reload = False
        self.irq_enable = False

    def write_reg(self, addr, val):
        a = addr & 0xE003
        if a == 0x8000:
            self.set_prg8(0, val & 0x3F)
            if not self.tc0690:
                self.mirror_vh(val & 0x40)
        elif a == 0x8001:
            self.set_prg8(1, val & 0x3F)
        elif a == 0x8002:
            self.set_chr2(0, val)
        elif a == 0x8003:
            self.set_chr2(1, val)
        elif 0xA000 <= a <= 0xA003:
            self.set_chr1(4 + (a & 3), val)
        elif self.tc0690:
            if a == 0xC000:
                self.irq_latch = (val ^ 0xFF) & 0xFF
            elif a == 0xC001:
                self.irq_reload = True
                self.irq_counter = 0
            elif a == 0xC002:
                self.irq_enable = True
            elif a == 0xC003:
                self.irq_enable = False
                self.irq_pending = False
            elif a == 0xE000:
                self.mirror_vh(val & 0x40)

    def scanline_tick(self):
        if not self.tc0690:
            return
        MMC3.scanline_tick(self)


class TaitoTC0690(TaitoTC0190):
    tc0690 = True


class TaitoX1005(Mapper):
    """Mapper 80 (and 207 with CHR-controlled nametables)."""

    def __init__(self, rom):
        super().__init__(rom)
        self.alt = rom.header.mapper == 207
        self.internal_ram = bytearray(128)
        self.ram_ok = False
        for i in range(3):
            self.set_prg8(i, 0)
        self.set_prg8(3, -1)

    def cpu_read(self, addr):
        if addr >= 0x8000:
            return self.prg[self.prg_map[(addr >> 13) & 3] | (addr & 0x1FFF)]
        if addr >= 0x7F00 and self.ram_ok:
            return self.internal_ram[addr & 0x7F]
        return addr >> 8

    def cpu_write(self, addr, val):
        if 0x7EF0 <= addr <= 0x7EFF:
            r = addr & 0x0F
            if r == 0:
                self.set_chr2(0, val >> 1)
                if self.alt:
                    p = self._ci[val >> 7]
                    self.nt[0] = self.nt[1] = p
            elif r == 1:
                self.set_chr2(1, val >> 1)
                if self.alt:
                    p = self._ci[val >> 7]
                    self.nt[2] = self.nt[3] = p
            elif r <= 5:
                self.set_chr1(r + 2, val)
            elif r <= 7:
                if not self.alt:
                    self.mirror_vh(not (val & 1))
            elif r <= 9:
                self.ram_ok = val == 0xA3
            else:
                self.set_prg8((r - 0x0A) >> 1, val)
        elif addr >= 0x7F00 and self.ram_ok:
            self.internal_ram[addr & 0x7F] = val

    def battery_data(self):
        return bytes(self.internal_ram)

    def load_battery(self, data):
        n = min(128, len(data))
        self.internal_ram[:n] = data[:n]


class TaitoX1017(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        self.inv = False
        self.chr_regs = [0] * 6
        for i in range(3):
            self.set_prg8(i, 0)
        self.set_prg8(3, -1)
        self._update_chr()

    def _update_chr(self):
        c = self.chr_regs
        b0 = 4 if self.inv else 0
        b1 = 0 if self.inv else 4
        self.set_chr1(b0, c[0] & 0xFE)
        self.set_chr1(b0 + 1, c[0] | 1)
        self.set_chr1(b0 + 2, c[1] & 0xFE)
        self.set_chr1(b0 + 3, c[1] | 1)
        for i in range(4):
            self.set_chr1(b1 + i, c[2 + i])

    def cpu_write(self, addr, val):
        if 0x7EF0 <= addr <= 0x7EFF:
            r = addr & 0x0F
            if r <= 5:
                self.chr_regs[r] = val
                self._update_chr()
            elif r == 6:
                self.mirror_vh(not (val & 1))
                self.inv = bool(val & 2)
                self._update_chr()
            elif 0x0A <= r <= 0x0C:
                self.set_prg8(r - 0x0A, val >> 2)
        elif 0x6000 <= addr < 0x7400:
            self.prg_ram[addr & 0x1FFF] = val


class Sunsoft3(Mapper):
    needs_cpu_clock = True

    def __init__(self, rom):
        super().__init__(rom)
        self.irq_enabled = False
        self.irq_counter = 0
        self.toggle = 0
        self.set_prg16(1, -1)

    def write_reg(self, addr, val):
        base = addr & 0xF800
        if base in (0x8800, 0x9800, 0xA800, 0xB800):
            self.set_chr2((base - 0x8800) >> 12, val)
        elif base == 0xC800:
            if self.toggle == 0:
                self.irq_counter = (self.irq_counter & 0x00FF) | (val << 8)
            else:
                self.irq_counter = (self.irq_counter & 0xFF00) | val
            self.toggle ^= 1
        elif base == 0xD800:
            self.irq_enabled = bool(val & 0x10)
            self.toggle = 0
            self.irq_pending = False
        elif base == 0xE800:
            self.mirror4(val)
        elif base == 0xF800:
            self.set_prg16(0, val)

    def cpu_clock(self, cycles):
        if self.irq_enabled:
            c = self.irq_counter - cycles
            if c < 0:
                self.irq_pending = True
                self.irq_enabled = False
                c &= 0xFFFF
            self.irq_counter = c


class Sunsoft4(Mapper):
    def __init__(self, rom):
        super().__init__(rom)
        self.nt_regs = [0x80, 0x80]
        self.nt_rom = False
        self.mirr = 0
        self.set_prg16(1, -1)

    def _update_nt(self):
        if not self.nt_rom:
            self.mirror4(self.mirr)
            return
        p0 = self.chr_page_copy(self.nt_regs[0])
        p1 = self.chr_page_copy(self.nt_regs[1])
        m = self.mirr
        if m == 0:
            self.nt = [p0, p1, p0, p1]
        elif m == 1:
            self.nt = [p0, p0, p1, p1]
        elif m == 2:
            self.nt = [p0] * 4
        else:
            self.nt = [p1] * 4

    def write_reg(self, addr, val):
        base = addr & 0xF000
        if base <= 0xB000:
            self.set_chr2((base - 0x8000) >> 12, val)
        elif base == 0xC000:
            self.nt_regs[0] = val | 0x80
            self._update_nt()
        elif base == 0xD000:
            self.nt_regs[1] = val | 0x80
            self._update_nt()
        elif base == 0xE000:
            self.mirr = val & 3
            self.nt_rom = bool(val & 0x10)
            self._update_nt()
        else:
            self.set_prg16(0, val & 0x0F)
            self.prg_ram_enabled = bool(val & 0x10)


_5B_VOL = tuple(0.0 if v == 0 else 0.09 * 10 ** ((v - 15) * 1.5 / 20.0)
                for v in range(16))


class FME7(Mapper):
    """Mapper 69: Sunsoft FME-7 / 5A / 5B (incl. 5B tone channels)."""
    needs_cpu_clock = True
    has_audio = True

    def __init__(self, rom):
        super().__init__(rom)
        self.cmd = 0
        self.ram_sel = False
        self.ram_en = False
        self.rom6000 = 0
        self.irq_enabled = False
        self.counter_enabled = False
        self.irq_counter = 0
        self.snd_addr = 0
        self.snd = bytearray(16)
        self.snd_timer = [1, 1, 1]
        self.snd_out = [0, 0, 0]
        self.set_prg8(3, -1)

    def cpu_read(self, addr):
        if addr >= 0x8000:
            return self.prg[self.prg_map[(addr >> 13) & 3] | (addr & 0x1FFF)]
        if addr >= 0x6000:
            if self.ram_sel:
                return self.prg_ram[addr & 0x1FFF] if self.ram_en else addr >> 8
            return self.prg[self.rom6000 | (addr & 0x1FFF)]
        return addr >> 8

    def cpu_write(self, addr, val):
        if addr >= 0x8000:
            self.write_reg(addr, val)
        elif addr >= 0x6000 and self.ram_sel and self.ram_en:
            self.prg_ram[addr & 0x1FFF] = val

    def write_reg(self, addr, val):
        base = addr & 0xE000
        if base == 0x8000:
            self.cmd = val & 0x0F
        elif base == 0xA000:
            c = self.cmd
            if c < 8:
                self.set_chr1(c, val)
            elif c == 8:
                self.ram_sel = bool(val & 0x40)
                self.ram_en = bool(val & 0x80)
                self.rom6000 = ((val & 0x3F) % self.prg_count8) << 13
            elif c <= 0x0B:
                self.set_prg8(c - 9, val & 0x3F)
            elif c == 0x0C:
                self.mirror4(val)
            elif c == 0x0D:
                self.irq_enabled = bool(val & 1)
                self.counter_enabled = bool(val & 0x80)
                self.irq_pending = False
            elif c == 0x0E:
                self.irq_counter = (self.irq_counter & 0xFF00) | val
            else:
                self.irq_counter = (self.irq_counter & 0x00FF) | (val << 8)
        elif base == 0xC000:
            self.snd_addr = val & 0x0F
        elif base == 0xE000:
            self.snd[self.snd_addr] = val

    def cpu_clock(self, cycles):
        if self.counter_enabled:
            c = self.irq_counter - cycles
            if c < 0:
                c &= 0xFFFF
                if self.irq_enabled:
                    self.irq_pending = True
            self.irq_counter = c

    def audio_clock(self, cycles):
        s = self.snd
        for ch in range(3):
            t = self.snd_timer[ch] - cycles
            if t <= 0:
                period = ((s[ch * 2] | ((s[ch * 2 + 1] & 0x0F) << 8)) or 1) * 16
                n = 1 + (-t) // period
                t += n * period
                if n & 1:
                    self.snd_out[ch] ^= 1
            self.snd_timer[ch] = t

    def audio_output(self):
        s = self.snd
        out = 0.0
        for ch in range(3):
            if not (s[7] & (1 << ch)) and self.snd_out[ch]:
                out += _5B_VOL[s[8 + ch] & 0x0F]
        return out


_MAPPER_TABLE = {
    0: NROM, 1: MMC1, 2: UxROM, 3: CNROM, 4: MMC3, 5: MMC5, 7: AxROM,
    9: MMC2, 10: MMC4, 11: ColorDreams, 13: CPROM, 16: BandaiFCG,
    18: JalecoSS88006, 19: Namco163, 21: VRC4, 22: VRC4, 23: VRC4, 24: VRC6,
    25: VRC4, 26: VRC6, 32: IremG101, 33: TaitoTC0190, 34: Mapper34,
    37: MMC3Multi37, 47: MMC3Multi47, 48: TaitoTC0690, 64: RAMBO1,
    65: IremH3001, 66: GxROM, 67: Sunsoft3, 68: Sunsoft4, 69: FME7,
    70: Bandai74161, 71: Camerica, 72: JalecoJF17, 73: VRC3, 75: VRC1,
    76: Namco3446, 77: Irem77, 78: Irem78, 79: NINA0306, 80: TaitoX1005,
    82: TaitoX1017, 85: VRC7, 86: JalecoJF13, 87: Jaleco87, 88: Namco88,
    89: Sunsoft89, 92: JalecoJF19, 93: Sunsoft93, 94: UN1ROM, 95: Namco3425,
    97: IremTAMS1, 113: NINA113, 118: TxSROM, 119: TQROM, 140: Jaleco140,
    152: Bandai152, 153: BandaiFCG, 154: Namco154, 155: MMC1, 159: BandaiFCG,
    180: UNROM180, 184: Sunsoft1, 185: CNROM185, 206: Namco108,
    207: TaitoX1005, 210: Namco163, 232: Camerica232,
}


def make_mapper(rom):
    cls = _MAPPER_TABLE.get(rom.header.mapper)
    if cls is None:
        return NROM(rom)
    return cls(rom)


# =============================================================================
#  PPU & APU — picture + native 2A03 audio synthesis (no audio files)
# =============================================================================

AUDIO_FILES = False
AUDIO_ENABLED = True
SAMPLE_RATE = 48000
CPU_HZ_NTSC = 1789773.0
PPU_SCANLINES = 262
PPU_DOTS_PER_LINE = 341

# Engine timing — NTSC core; display locked to 60.00 Hz in the GUI loop.
TARGET_FPS = 60.0
FRAME_SEC = 1.0 / TARGET_FPS
NTSC_CPU_CYCLES_PER_FRAME = PPU_SCANLINES * (PPU_DOTS_PER_LINE / 3.0)
NTSC_CYCLES_PER_SCANLINE = NTSC_CPU_CYCLES_PER_FRAME / PPU_SCANLINES
# The GUI intentionally runs at exactly 60.00 FPS.  Sampling against the
# emulated clock keeps the native audio device fed with exactly 800 samples per
# displayed frame, avoiding the slow underrun that occurs when 60.00 Hz video
# is paired with the NES's 60.0988 Hz crystal rate.
EMULATED_CPU_HZ = NTSC_CPU_CYCLES_PER_FRAME * TARGET_FPS

_PATTERN_ROW_CACHE = {}
_IDENTITY_TRANSLATION = bytes(range(256))


def _decode_pattern_row(lo, hi):
    """Expand two NES bitplanes once, then reuse the eight decoded pixels."""
    key = (lo << 8) | hi
    row = _PATTERN_ROW_CACHE.get(key)
    if row is None:
        row = bytes(
            ((lo >> bit) & 1) | (((hi >> bit) & 1) << 1)
            for bit in range(7, -1, -1)
        )
        if len(_PATTERN_ROW_CACHE) >= 8192:
            _PATTERN_ROW_CACHE.clear()
        _PATTERN_ROW_CACHE[key] = row
    return row


_GREYSCALE = bytes(i & 0x30 for i in range(256))
_ZERO8 = bytes(8)


class PPU:
    """Scanline PPU driven by the real loopy v/t/x scroll registers.

    Each visible line is rendered at its start from the current v (so mid-frame
    $2005/$2006 splits, MMC3 IRQ splits and sprite-0 splits land on the right
    line); dot-256/257 increments and t->v copies happen in end_line().
    """

    def __init__(self, mapper):
        self.mapper = mapper
        self.apu = None
        self.cpu = None
        self.palette = bytearray(32)
        self.oam = bytearray(256)
        self.framebuffer = bytearray(256 * 240)
        self.scanline = 0
        self.frame = 0
        self.ctrl = 0
        self.mask = 0
        self.status = 0
        self.oam_addr = 0
        self.v = 0
        self.t = 0
        self.x = 0
        self.w = 0
        self.buffer = 0
        self.open_bus = 0
        self.nmi = False
        self.odd_frame = False
        self.hit_cycle = -1.0
        self._bg_lut_key = None
        self._bg_luts = None
        self._colored_row_cache = {}
        self._row = bytearray(264)
        self._bgp = bytearray(264)
        self._fetch_hook = mapper.set_fetch if mapper.split_chr else None
        self._ovf_key = None
        self._ovf_counts = None
        init = [0x09,0x01,0x00,0x01,0x00,0x02,0x02,0x0D,
                0x08,0x10,0x08,0x24,0x00,0x00,0x04,0x2C,
                0x09,0x01,0x34,0x03,0x00,0x04,0x00,0x14,
                0x00,0x00,0x00,0x05,0x00,0x00,0x00,0x00]
        for i, v in enumerate(init):
            self.palette[i] = v

    def _background_luts(self):
        key = bytes(self.palette[:16])
        if key != self._bg_lut_key:
            universal = self.palette[0] & 0x3F
            luts = []
            for pal_hi in (0, 4, 8, 12):
                lut = bytearray(_IDENTITY_TRANSLATION)
                lut[0] = universal
                lut[1] = self.palette[pal_hi | 1] & 0x3F
                lut[2] = self.palette[pal_hi | 2] & 0x3F
                lut[3] = self.palette[pal_hi | 3] & 0x3F
                luts.append(bytes(lut))
            self._bg_lut_key = key
            self._bg_luts = tuple(luts)
            self._colored_row_cache.clear()
        return self._bg_luts

    # -- PPU address space -----------------------------------------------------
    def ppu_read(self, addr):
        addr &= 0x3FFF
        if addr < 0x2000:
            return self.mapper.ppu_read(addr)
        if addr < 0x3F00:
            return self.mapper.nt[(addr >> 10) & 3][addr & 0x3FF]
        a = addr & 0x1F
        if (a & 0x13) == 0x10:
            a &= 0x0F
        return self.palette[a] & 0x3F

    def ppu_write(self, addr, val):
        addr &= 0x3FFF
        if addr < 0x2000:
            self.mapper.ppu_write(addr, val)
        elif addr < 0x3F00:
            self.mapper.nt[(addr >> 10) & 3][addr & 0x3FF] = val
        else:
            a = addr & 0x1F
            if (a & 0x13) == 0x10:
                a &= 0x0F
            self.palette[a] = val & 0x3F

    # -- CPU-visible registers ---------------------------------------------------
    def reg_read(self, reg):
        reg &= 7
        if reg == 2:
            if (self.hit_cycle >= 0 and self.cpu is not None
                    and self.cpu.cycles >= self.hit_cycle):
                self.status |= 0x40
                self.hit_cycle = -1.0
            v = (self.status & 0xE0) | (self.open_bus & 0x1F)
            self.status &= 0x7F
            self.w = 0
            self.open_bus = v
            return v
        if reg == 4:
            v = self.oam[self.oam_addr]
            if (self.oam_addr & 3) == 2:
                v &= 0xE3
            self.open_bus = v
            return v
        if reg == 7:
            addr = self.v & 0x3FFF
            if addr < 0x3F00:
                ret = self.buffer
                self.buffer = self.ppu_read(addr)
            else:
                ret = (self.ppu_read(addr) & 0x3F) | (self.open_bus & 0xC0)
                self.buffer = self.ppu_read(addr - 0x1000)
            self._set_v((self.v + (32 if (self.ctrl & 4) else 1)) & 0x7FFF)
            self.open_bus = ret
            return ret
        return self.open_bus

    def reg_write(self, reg, val):
        reg &= 7
        self.open_bus = val
        if reg == 0:
            old = self.ctrl
            self.ctrl = val
            self.t = (self.t & 0x73FF) | ((val & 3) << 10)
            if (val & 0x80) and not (old & 0x80) and (self.status & 0x80) \
                    and self.cpu is not None:
                self.cpu.pending_nmi = True
        elif reg == 1:
            self.mask = val
        elif reg == 3:
            self.oam_addr = val
        elif reg == 4:
            self.oam[self.oam_addr] = val
            self.oam_addr = (self.oam_addr + 1) & 0xFF
        elif reg == 5:
            if self.w == 0:
                self.t = (self.t & 0x7FE0) | (val >> 3)
                self.x = val & 7
                self.w = 1
            else:
                self.t = (self.t & 0x0C1F) | ((val & 7) << 12) | ((val & 0xF8) << 2)
                self.w = 0
        elif reg == 6:
            if self.w == 0:
                self.t = (self.t & 0x00FF) | ((val & 0x3F) << 8)
                self.w = 1
            else:
                self.t = (self.t & 0x7F00) | val
                self._set_v(self.t)
                self.w = 0
        elif reg == 7:
            self.ppu_write(self.v & 0x3FFF, val)
            self._set_v((self.v + (32 if (self.ctrl & 4) else 1)) & 0x7FFF)

    def _set_v(self, v):
        # Outside rendering, PPUADDR/PPUDATA traffic drives A12 directly.
        if (v & 0x1000) and not (self.v & 0x1000) and not (self.mask & 0x18):
            self.mapper.a12_rise()
        self.v = v

    def oam_dma_write(self, data):
        a = self.oam_addr
        for b in data:
            self.oam[a] = b
            a = (a + 1) & 0xFF

    # -- rendering -----------------------------------------------------------------
    def _render_line(self, y, start):
        mapper = self.mapper
        mask = self.mask
        ctrl = self.ctrl
        hook = self._fetch_hook
        large = ctrl & 0x20
        universal = self.palette[0] & 0x3F
        bg_on = mask & 0x08
        sp_on = mask & 0x10
        if bg_on:
            if hook is not None:
                hook(0, large)
            row = self._row
            bgp = self._bgp
            v = self.v
            fine_y = (v >> 12) & 7
            pt = (0x1000 if ctrl & 0x10 else 0) | fine_y
            nt = mapper.nt
            read = mapper.ppu_read
            luts = self._background_luts()
            cache = self._colored_row_cache
            ext = mapper.ext_attr if mapper.exram_mode == 1 else None
            for sx in range(0, 264, 8):
                page = nt[(v >> 10) & 3]
                off = v & 0x3FF
                tile = page[off]
                if ext is None:
                    at = page[0x3C0 | ((v >> 4) & 0x38) | ((v >> 2) & 7)]
                    pal = (at >> (((v >> 4) & 4) | (v & 2))) & 3
                    a = pt | (tile << 4)
                    lo = read(a)
                    hi = read(a | 8)
                else:
                    lo, hi, pal = ext(off, tile, fine_y)
                key = (lo << 10) | (hi << 2) | pal
                colored = cache.get(key)
                if colored is None:
                    colored = _decode_pattern_row(lo, hi).translate(luts[pal])
                    if len(cache) >= 16384:
                        cache.clear()
                    cache[key] = colored
                row[sx:sx + 8] = colored
                if sp_on:
                    bgp[sx:sx + 8] = _decode_pattern_row(lo, hi)
                if (v & 0x1F) == 31:
                    v = (v & 0x7FE0) ^ 0x0400
                else:
                    v += 1
            fx = self.x
            if not (mask & 0x02):
                row[fx:fx + 8] = bytes((universal,)) * 8
                if sp_on:
                    bgp[fx:fx + 8] = _ZERO8
            out = row[fx:fx + 256]
            bgo = bgp[fx:fx + 256] if sp_on else None
        else:
            out = bytearray((universal,)) * 256
            bgo = bytearray(256)
        if sp_on:
            self._render_sprites(y, start, out, bgo, bool(bg_on), large, hook)
        if mask & 0x01:
            out = out.translate(_GREYSCALE)
        base = y << 8
        self.framebuffer[base:base + 256] = out
        if hook is not None:
            hook(2, large)

    def _render_sprites(self, y, start, out, bgo, bg_on, large, hook):
        if hook is not None:
            hook(1, large)
        oam = self.oam
        palette = self.palette
        read = self.mapper.ppu_read
        h = 16 if large else 8
        sp_pt = 0x1000 if (self.ctrl & 0x08) else 0
        clip = 0 if (self.mask & 0x04) else 8
        drawn = bytearray(256)
        count = 0
        hit = -1
        for i in range(0, 256, 4):
            dy = y - oam[i] - 1
            if dy < 0 or dy >= h:
                continue
            if count == 8:
                break
            count += 1
            tile = oam[i + 1]
            attr = oam[i + 2]
            sx = oam[i + 3]
            if attr & 0x80:
                dy = h - 1 - dy
            if large:
                a = (((tile & 1) << 12) | ((tile & 0xFE) << 4)
                     | ((dy & 8) << 1) | (dy & 7))
            else:
                a = sp_pt | (tile << 4) | dy
            lo = read(a)
            hi = read(a | 8)
            if not (lo | hi):
                continue
            pattern = _decode_pattern_row(lo, hi)
            if attr & 0x40:
                pattern = pattern[::-1]
            pal = 0x10 | ((attr & 3) << 2)
            behind = attr & 0x20
            for px in range(8):
                p = pattern[px]
                if not p:
                    continue
                xx = sx + px
                if xx > 255:
                    break
                if xx < clip or drawn[xx]:
                    continue
                drawn[xx] = 1
                bgpix = bgo[xx]
                if i == 0 and bgpix and hit < 0 and bg_on and xx != 255:
                    hit = xx
                if behind and bgpix:
                    continue
                out[xx] = palette[pal | p] & 0x3F
        if hit >= 0 and not (self.status & 0x40) and self.hit_cycle < 0:
            self.hit_cycle = start + (hit + 2) / 3.0

    def _eval_overflow(self, line):
        h = 16 if (self.ctrl & 0x20) else 8
        key = (bytes(self.oam[0::4]), h)
        if key != self._ovf_key:
            counts = bytearray(256)
            for yy in key[0]:
                for k in range(yy, min(yy + h, 256)):
                    counts[k] += 1
            self._ovf_key = key
            self._ovf_counts = counts
        if self._ovf_counts[line] > 8:
            self.status |= 0x20

    # -- scanline timing -----------------------------------------------------------
    def begin_line(self, line, start):
        """Dot 0..1 of `line`; `start` is the CPU cycle the line begins on."""
        self.scanline = line
        if line < 240:
            if self.mask & 0x18:
                if not (self.status & 0x20):
                    self._eval_overflow(line)
                self._render_line(line, start)
            else:
                base = line << 8
                self.framebuffer[base:base + 256] = \
                    bytes((self.palette[0] & 0x3F,)) * 256
        elif line == 241:
            self.status |= 0x80
            if (self.ctrl & 0x80) and self.cpu is not None:
                self.cpu.pending_nmi = True
        elif line == 261:
            self.status &= 0x1F
            self.hit_cycle = -1.0

    def end_line(self, line):
        """Dots 256-260: y increment, horizontal (and pre-render vertical) copy."""
        rendering = self.mask & 0x18
        if rendering:
            if line < 240:
                v = self.v
                if (v & 0x7000) != 0x7000:
                    v += 0x1000
                else:
                    v &= 0x0FFF
                    cy = (v >> 5) & 0x1F
                    if cy == 29:
                        cy = 0
                        v ^= 0x0800
                    elif cy == 31:
                        cy = 0
                    else:
                        cy += 1
                    v = (v & 0x7C1F) | (cy << 5)
                self.v = (v & 0x7BE0) | (self.t & 0x041F)
            elif line == 261:
                self.v = self.t
        self.mapper.on_scanline(line, bool(rendering))
        if line == 261:
            self.frame += 1
            self.odd_frame = not self.odd_frame
            if self.apu is not None:
                self.apu.on_ppu_frame(self.frame)


# --- APU (2A03 audio synthesis) ---

_LENGTH_TABLE = (
    10, 254, 20, 2, 40, 4, 80, 6, 160, 8, 60, 10, 14, 12, 26, 14,
    12, 16, 24, 18, 48, 20, 96, 22, 192, 24, 72, 26, 16, 28, 32, 30,
)

_NOISE_PERIOD_NTSC = (
    4, 8, 16, 32, 64, 96, 128, 160,
    202, 254, 380, 508, 762, 1016, 2034, 4068,
)

_DMC_RATE_NTSC = (
    428, 380, 340, 320, 286, 254, 226, 214, 190, 160, 142, 128, 106, 84, 72, 54,
)

_DUTY_SEQ = (
    (0, 1, 0, 0, 0, 0, 0, 0),
    (0, 1, 1, 0, 0, 0, 0, 0),
    (0, 1, 1, 1, 1, 0, 0, 0),
    (1, 0, 0, 1, 1, 1, 1, 1),
)

# CPU-cycle positions of the 2A03 frame sequencer.  Channel behavior and the
# lookup tables here were cross-checked against FCEUX's src/sound.cpp; this is
# a clean Python implementation rather than embedded FCEUX/C++ code.
_FRAME_STEPS_4 = (
    (3729, True, False),
    (7457, True, True),
    (11186, True, False),
    (14915, True, True),
)
_FRAME_STEPS_5 = (
    (3729, True, False),
    (7457, True, True),
    (11186, True, False),
    (14915, False, False),
    (18641, True, True),
)


class _Pulse:
    __slots__ = (
        "enabled", "channel", "timer", "timer_period", "duty", "duty_step",
        "length_counter", "length_halt", "volume", "constant_volume",
        "envelope_loop", "envelope_start", "envelope_divider", "envelope_counter",
        "sweep_enabled", "sweep_period", "sweep_negate", "sweep_shift",
        "sweep_reload", "sweep_divider", "sweep_counter", "target_period",
    )

    def __init__(self, channel):
        self.channel = channel
        self.reset()

    def reset(self):
        self.enabled = False
        self.timer = 0
        self.timer_period = 0
        self.duty = 0
        self.duty_step = 0
        self.length_counter = 0
        self.length_halt = False
        self.volume = 0
        self.constant_volume = False
        self.envelope_loop = False
        self.envelope_start = False
        self.envelope_divider = 0
        self.envelope_counter = 0
        self.sweep_enabled = False
        self.sweep_period = 0
        self.sweep_negate = False
        self.sweep_shift = 0
        self.sweep_reload = False
        self.sweep_divider = 0
        self.sweep_counter = 0
        self.target_period = 0

    def write_reg0(self, val):
        self.duty = (val >> 6) & 3
        self.length_halt = bool(val & 0x20)
        self.envelope_loop = bool(val & 0x20)
        self.constant_volume = bool(val & 0x10)
        self.volume = val & 0x0F

    def write_reg1(self, val):
        self.sweep_enabled = bool(val & 0x80)
        self.sweep_period = (val >> 4) & 7
        self.sweep_negate = bool(val & 0x08)
        self.sweep_shift = val & 7
        self.sweep_reload = True
        self._update_target()

    def write_reg2(self, val):
        self.timer_period = (self.timer_period & 0x700) | val
        self._update_target()

    def write_reg3(self, val):
        self.timer_period = (self.timer_period & 0xFF) | ((val & 7) << 8)
        if self.enabled:
            self.length_counter = _LENGTH_TABLE[(val >> 3) & 0x1F]
        self.duty_step = 0
        self.timer = 0
        self.envelope_start = True
        self._update_target()

    def _update_target(self):
        change = self.timer_period >> self.sweep_shift
        if self.sweep_negate:
            if self.channel == 0:
                change = -change - 1
            else:
                change = -change
        self.target_period = self.timer_period + change

    def clock_timer(self, cycles=1):
        period = (self.timer_period + 1) * 2
        if cycles <= self.timer:
            self.timer -= cycles
            return
        remaining = cycles - self.timer - 1
        steps = 1 + remaining // period
        self.timer = period - 1 - (remaining % period)
        self.duty_step = (self.duty_step + steps) & 7

    def clock_envelope(self):
        if self.envelope_start:
            self.envelope_start = False
            self.envelope_counter = 15
            self.envelope_divider = self.volume
        elif self.envelope_divider:
            self.envelope_divider -= 1
        else:
            self.envelope_divider = self.volume
            if self.envelope_counter:
                self.envelope_counter -= 1
            elif self.envelope_loop:
                self.envelope_counter = 15

    def clock_length(self):
        if not self.length_halt and self.length_counter:
            self.length_counter -= 1

    def clock_sweep(self):
        if self.sweep_divider == 0:
            if self.sweep_enabled and self.sweep_shift and self.timer_period >= 8:
                if 0 < self.target_period <= 0x7FF:
                    self.timer_period = self.target_period
                    self._update_target()
        if self.sweep_divider == 0 or self.sweep_reload:
            self.sweep_divider = self.sweep_period
            self.sweep_reload = False
        else:
            self.sweep_divider -= 1

    def output(self):
        if not self.enabled or not self.length_counter or self.timer_period < 8:
            return 0
        if self.sweep_enabled and not (0 <= self.target_period <= 0x7FF):
            return 0
        seq = _DUTY_SEQ[self.duty][self.duty_step]
        if not seq:
            return 0
        if self.constant_volume:
            return self.volume
        return self.envelope_counter


class _Triangle:
    __slots__ = (
        "enabled", "timer", "timer_period", "length_counter", "length_halt",
        "linear_counter", "linear_reload_value", "linear_reload_flag",
        "control_flag", "step",
    )

    def __init__(self):
        self.reset()

    def reset(self):
        self.enabled = False
        self.timer = 0
        self.timer_period = 0
        self.length_counter = 0
        self.length_halt = False
        self.linear_counter = 0
        self.linear_reload_value = 0
        self.linear_reload_flag = False
        self.control_flag = False
        self.step = 0

    def write_reg0(self, val):
        self.control_flag = bool(val & 0x80)
        self.length_halt = self.control_flag
        self.linear_reload_value = val & 0x7F

    def write_reg2(self, val):
        self.timer_period = (self.timer_period & 0x700) | val

    def write_reg3(self, val):
        self.timer_period = (self.timer_period & 0xFF) | ((val & 7) << 8)
        if self.enabled:
            self.length_counter = _LENGTH_TABLE[(val >> 3) & 0x1F]
        self.linear_reload_flag = True

    def clock_timer(self, cycles=1):
        period = self.timer_period + 1
        if cycles <= self.timer:
            self.timer -= cycles
            return
        remaining = cycles - self.timer - 1
        steps = 1 + remaining // period
        self.timer = period - 1 - (remaining % period)
        if self.timer_period >= 2 and self.linear_counter and self.length_counter:
            self.step = (self.step + steps) & 31

    def clock_linear(self):
        if self.linear_reload_flag:
            self.linear_counter = self.linear_reload_value
        elif self.linear_counter:
            self.linear_counter -= 1
        if not self.control_flag:
            self.linear_reload_flag = False

    def clock_length(self):
        if not self.length_halt and self.length_counter:
            self.length_counter -= 1

    def output(self):
        if not self.enabled or not self.length_counter or not self.linear_counter:
            return 0
        if self.timer_period < 2:
            return 7
        step = self.step
        if step < 16:
            return step
        return 31 - step


class _Noise:
    __slots__ = (
        "enabled", "timer", "timer_period", "mode", "shift", "length_counter",
        "length_halt", "volume", "constant_volume", "envelope_loop",
        "envelope_start", "envelope_divider", "envelope_counter",
    )

    def __init__(self):
        self.reset()

    def reset(self):
        self.enabled = False
        self.timer = 0
        self.timer_period = 0
        self.mode = 0
        self.shift = 1
        self.length_counter = 0
        self.length_halt = False
        self.volume = 0
        self.constant_volume = False
        self.envelope_loop = False
        self.envelope_start = False
        self.envelope_divider = 0
        self.envelope_counter = 0

    def write_reg0(self, val):
        self.length_halt = bool(val & 0x20)
        self.envelope_loop = bool(val & 0x20)
        self.constant_volume = bool(val & 0x10)
        self.volume = val & 0x0F

    def write_reg2(self, val):
        self.mode = (val >> 7) & 1
        self.timer_period = _NOISE_PERIOD_NTSC[val & 0x0F]

    def write_reg3(self, val):
        if self.enabled:
            self.length_counter = _LENGTH_TABLE[(val >> 3) & 0x1F]
        self.envelope_start = True

    def clock_timer(self, cycles=1):
        period = max(1, self.timer_period)
        if cycles <= self.timer:
            self.timer -= cycles
            return
        remaining = cycles - self.timer - 1
        steps = 1 + remaining // period
        self.timer = period - 1 - (remaining % period)
        tap = 6 if self.mode else 1
        for _ in range(steps):
            feedback = (self.shift & 1) ^ ((self.shift >> tap) & 1)
            self.shift = (self.shift >> 1) | (feedback << 14)

    def clock_envelope(self):
        if self.envelope_start:
            self.envelope_start = False
            self.envelope_counter = 15
            self.envelope_divider = self.volume
        elif self.envelope_divider:
            self.envelope_divider -= 1
        else:
            self.envelope_divider = self.volume
            if self.envelope_counter:
                self.envelope_counter -= 1
            elif self.envelope_loop:
                self.envelope_counter = 15

    def clock_length(self):
        if not self.length_halt and self.length_counter:
            self.length_counter -= 1

    def output(self):
        if not self.enabled or not self.length_counter or (self.shift & 1):
            return 0
        if self.constant_volume:
            return self.volume
        return self.envelope_counter


class _DMC:
    __slots__ = (
        "enabled", "irq_enabled", "loop", "rate_index", "timer", "rate_period",
        "output_level", "sample_addr", "sample_length", "current_addr",
        "bytes_remaining", "shift", "bits_remaining", "silence", "irq_pending",
        "sample_buffer", "sample_buffer_empty", "bus",
    )

    def __init__(self):
        self.bus = None
        self.reset()

    def reset(self):
        self.enabled = False
        self.irq_enabled = False
        self.loop = False
        self.rate_index = 0
        self.timer = 0
        self.rate_period = _DMC_RATE_NTSC[0]
        self.output_level = 0
        self.sample_addr = 0
        self.sample_length = 0
        self.current_addr = 0
        self.bytes_remaining = 0
        self.shift = 0
        self.bits_remaining = 0
        self.silence = True
        self.irq_pending = False
        self.sample_buffer = 0
        self.sample_buffer_empty = True

    def write_reg0(self, val):
        self.irq_enabled = bool(val & 0x80)
        self.loop = bool(val & 0x40)
        self.rate_index = val & 0x0F
        self.rate_period = _DMC_RATE_NTSC[self.rate_index]
        if not self.irq_enabled:
            self.irq_pending = False

    def write_reg1(self, val):
        self.output_level = val & 0x7F

    def write_reg2(self, val):
        self.sample_addr = 0xC000 | (val << 6)

    def write_reg3(self, val):
        self.sample_length = (val << 4) | 1

    def start(self):
        if not self.bytes_remaining:
            self.current_addr = self.sample_addr
            self.bytes_remaining = self.sample_length
        self._fill_sample_buffer()

    def clock_timer(self, cycles=1):
        if self.sample_buffer_empty and self.bytes_remaining:
            self._fill_sample_buffer()
        period = max(1, self.rate_period)
        if cycles <= self.timer:
            self.timer -= cycles
            return
        remaining = cycles - self.timer - 1
        steps = 1 + remaining // period
        self.timer = period - 1 - (remaining % period)
        for _ in range(steps):
            if not self.silence:
                if self.shift & 1:
                    if self.output_level <= 125:
                        self.output_level += 2
                elif self.output_level >= 2:
                    self.output_level -= 2
                self.shift >>= 1
            if self.bits_remaining:
                self.bits_remaining -= 1
            if not self.bits_remaining:
                self.bits_remaining = 8
                if self.sample_buffer_empty:
                    self.silence = True
                else:
                    self.silence = False
                    self.shift = self.sample_buffer
                    self.sample_buffer_empty = True
                self._fill_sample_buffer()

    def _fill_sample_buffer(self):
        if not self.enabled or not self.sample_buffer_empty:
            return
        if not self.bytes_remaining:
            return
        if self.bus is not None:
            self.sample_buffer = self.bus.read(self.current_addr)
            if hasattr(self.bus, "dma_stall"):
                self.bus.dma_stall += 4
        else:
            self.sample_buffer = 0
        self.sample_buffer_empty = False
        self.current_addr = 0x8000 if self.current_addr == 0xFFFF else self.current_addr + 1
        self.bytes_remaining -= 1
        if not self.bytes_remaining:
            if self.loop:
                self.current_addr = self.sample_addr
                self.bytes_remaining = self.sample_length
            else:
                if self.irq_enabled:
                    self.irq_pending = True

    def output(self):
        # $4011 is a direct DAC load, so its level remains in the mixer even
        # when the DMC sample reader is disabled through $4015.
        return self.output_level


def _mix_channels(p1, p2, tri, noise, dmc):
    pulse = p1 + p2
    if pulse:
        pulse_out = 95.52 / (8128.0 / pulse + 100.0)
    else:
        pulse_out = 0.0
    tnd_input = tri / 8227.0 + noise / 12241.0 + dmc / 22638.0
    if tnd_input:
        tnd_out = 159.79 / (1.0 / tnd_input + 100.0)
    else:
        tnd_out = 0.0
    return pulse_out + tnd_out


class APU:
    def __init__(self):
        self.bus = None
        self.audio = None
        self.exp_audio = None
        self.reg = bytearray(0x18)
        self.pulse1 = _Pulse(0)
        self.pulse2 = _Pulse(1)
        self.triangle = _Triangle()
        self.noise = _Noise()
        self.dmc = _DMC()
        self.frame_mode = 0
        self.frame_irq_inhibit = False
        self.frame_irq_pending = False
        self.frame_step = 0
        self.frame_counter = 0
        self.frame_reset_delay = 0
        self.cpu_cycles = 0
        self._pending_cycles = 0
        self._batch_cycles = 32
        self.sample_accum = 0.0
        self.cycles_per_sample = EMULATED_CPU_HZ / SAMPLE_RATE
        self._sample_count = 0
        self._filter_in = 0.0
        self._filter_high = 0.0
        self._filter_low = 0.0
        self._high_pass_r = math.exp(-2.0 * math.pi * 90.0 / SAMPLE_RATE)
        self._low_pass_a = 1.0 - math.exp(-2.0 * math.pi * 14000.0 / SAMPLE_RATE)
        self._reset_channels()

    def _reset_channels(self):
        self.pulse1.reset()
        self.pulse2.reset()
        self.triangle.reset()
        self.noise.reset()
        self.dmc.reset()
        self.dmc.bus = self.bus

    def write(self, addr, val):
        self._flush_pending()
        val &= 0xFF
        if addr == 0x4017:
            self.frame_irq_inhibit = bool(val & 0x40)
            self.frame_mode = bool(val & 0x80)
            if self.frame_irq_inhibit:
                self.frame_irq_pending = False
            # The hardware applies a $4017 reset three or four CPU cycles
            # later depending on phase.  Keeping the delay prevents envelope
            # clicks in games that rewrite the frame counter mid-note.
            self.frame_reset_delay = 3 if (self.cpu_cycles & 1) else 4
            return
        addr -= 0x4000
        if 0 <= addr < len(self.reg):
            self.reg[addr] = val
        if addr == 0x15:
            self.pulse1.enabled = bool(val & 0x01)
            self.pulse2.enabled = bool(val & 0x02)
            self.triangle.enabled = bool(val & 0x04)
            self.noise.enabled = bool(val & 0x08)
            self.dmc.enabled = bool(val & 0x10)
            if not self.pulse1.enabled:
                self.pulse1.length_counter = 0
            if not self.pulse2.enabled:
                self.pulse2.length_counter = 0
            if not self.triangle.enabled:
                self.triangle.length_counter = 0
            if not self.noise.enabled:
                self.noise.length_counter = 0
            self.dmc.irq_pending = False
            if val & 0x10:
                self.dmc.start()
            else:
                self.dmc.bytes_remaining = 0
            return
        if addr <= 0x03:
            (self.pulse1.write_reg0, self.pulse1.write_reg1,
             self.pulse1.write_reg2, self.pulse1.write_reg3)[addr](val)
        elif addr <= 0x07:
            off = addr - 4
            (self.pulse2.write_reg0, self.pulse2.write_reg1,
             self.pulse2.write_reg2, self.pulse2.write_reg3)[off](val)
        elif addr <= 0x0B:
            off = addr - 8
            if off == 0:
                self.triangle.write_reg0(val)
            elif off == 2:
                self.triangle.write_reg2(val)
            elif off == 3:
                self.triangle.write_reg3(val)
        elif addr <= 0x0F:
            off = addr - 0x0C
            if off == 0:
                self.noise.write_reg0(val)
            elif off == 2:
                self.noise.write_reg2(val)
            elif off == 3:
                self.noise.write_reg3(val)
        elif addr <= 0x13:
            off = addr - 0x10
            (self.dmc.write_reg0, self.dmc.write_reg1,
             self.dmc.write_reg2, self.dmc.write_reg3)[off](val)

    def read_status(self):
        self._flush_pending()
        status = 0
        if self.pulse1.length_counter:
            status |= 0x01
        if self.pulse2.length_counter:
            status |= 0x02
        if self.triangle.length_counter:
            status |= 0x04
        if self.noise.length_counter:
            status |= 0x08
        if self.dmc.bytes_remaining:
            status |= 0x10
        if self.frame_irq_pending:
            status |= 0x40
        if self.dmc.irq_pending:
            status |= 0x80
        self.frame_irq_pending = False
        return status

    def _quarter_frame(self):
        self.pulse1.clock_envelope()
        self.pulse2.clock_envelope()
        self.triangle.clock_linear()
        self.noise.clock_envelope()

    def _half_frame(self):
        self.pulse1.clock_length()
        self.pulse2.clock_length()
        self.triangle.clock_length()
        self.noise.clock_length()
        self.pulse1.clock_sweep()
        self.pulse2.clock_sweep()

    def _frame_sequencer(self):
        steps = _FRAME_STEPS_5 if self.frame_mode else _FRAME_STEPS_4
        while self.frame_step < len(steps):
            cycle, quarter, half = steps[self.frame_step]
            if self.frame_counter < cycle:
                break
            if quarter:
                self._quarter_frame()
            if half:
                self._half_frame()
            if (not self.frame_mode and self.frame_step == 3
                    and not self.frame_irq_inhibit):
                self.frame_irq_pending = True
            self.frame_step += 1
            if self.frame_step >= len(steps):
                self.frame_counter = max(0, self.frame_counter - cycle)
                self.frame_step = 0
                break

    def _emit_sample(self):
        if not AUDIO_ENABLED or self.audio is None:
            return
        if AUDIO_FILES:
            return
        mixed = _mix_channels(
            self.pulse1.output(), self.pulse2.output(),
            self.triangle.output(), self.noise.output(), self.dmc.output(),
        )
        if self.exp_audio is not None:
            mixed += self.exp_audio.audio_output()
        # FCEUX also filters the raw nonlinear APU mix.  A lightweight
        # high-pass/low-pass pair removes the DAC's DC offset and ultrasonic
        # stair-stepping before feeding the native PCM backend.
        high = mixed - self._filter_in + self._high_pass_r * self._filter_high
        self._filter_in = mixed
        self._filter_high = high
        self._filter_low += self._low_pass_a * (high - self._filter_low)
        self.audio.push(self._filter_low)
        self._sample_count += 1

    def on_ppu_frame(self, ppu_frame):
        """PPU hook retained for mapper/debug compatibility; audio is CPU-clocked."""
        self._flush_pending()

    def _flush_pending(self):
        cycles = self._pending_cycles
        if not cycles:
            return
        self._pending_cycles = 0
        # CPU writes are instruction-granular in this compact emulator, so the
        # five timers can safely advance as a batch here.  This preserves the
        # channel phase while avoiding ~1.8 million Python loop iterations/s.
        if self.pulse1.enabled:
            self.pulse1.clock_timer(cycles)
        if self.pulse2.enabled:
            self.pulse2.clock_timer(cycles)
        if self.triangle.enabled:
            self.triangle.clock_timer(cycles)
        if self.noise.enabled:
            self.noise.clock_timer(cycles)
        if self.dmc.enabled or not self.dmc.silence:
            self.dmc.clock_timer(cycles)
        if self.exp_audio is not None:
            self.exp_audio.audio_clock(cycles)
        self.sample_accum += cycles

        if self.frame_reset_delay:
            delay = self.frame_reset_delay
            self.frame_reset_delay -= cycles
            if self.frame_reset_delay <= 0:
                self.frame_reset_delay = 0
                self.frame_counter = 0
                self.frame_step = 0
                if self.frame_mode:
                    self._quarter_frame()
                    self._half_frame()
                self.frame_counter = max(0, cycles - delay)
                if self.frame_counter:
                    self._frame_sequencer()
        else:
            self.frame_counter += cycles
            steps = _FRAME_STEPS_5 if self.frame_mode else _FRAME_STEPS_4
            if self.frame_counter >= steps[self.frame_step][0]:
                self._frame_sequencer()

        if self.sample_accum >= self.cycles_per_sample:
            sample_count = int(self.sample_accum / self.cycles_per_sample)
            self.sample_accum -= sample_count * self.cycles_per_sample
            if self.audio is not None:
                for _ in range(sample_count):
                    self._emit_sample()

    def clock(self, cycles=1):
        cycles = max(0, int(cycles))
        if not cycles:
            return
        self.cpu_cycles += cycles
        if cycles >= self._batch_cycles:
            remaining = cycles
            while remaining:
                room = self._batch_cycles - self._pending_cycles
                step = min(remaining, room)
                self._pending_cycles += step
                remaining -= step
                if self._pending_cycles >= self._batch_cycles:
                    self._flush_pending()
            if (self.frame_reset_delay
                    and self._pending_cycles >= self.frame_reset_delay):
                self._flush_pending()
            return
        self._pending_cycles += cycles
        if (self._pending_cycles >= self._batch_cycles
                or (self.frame_reset_delay
                    and self._pending_cycles >= self.frame_reset_delay)):
            self._flush_pending()

    def irq_pending(self):
        self._flush_pending()
        return self.frame_irq_pending or self.dmc.irq_pending


class _LegacyWinMMAudioStream:
    """PCM output via WinMM waveOut on Windows."""

    _CHUNK = 512
    _POOL = 4
    _MIN_START = 64
    WHDR_DONE = 0x00000001
    AUDIO_GAIN = 5.0

    def __init__(self, rate=SAMPLE_RATE):
        self.rate = rate
        self._queue = deque(maxlen=32768)
        self._lock = threading.Lock()
        self._alive = False
        self._hwo = None
        self._winmm = None
        self._pool = []
        self._pool_free = set()
        self._due_at = {}
        self._WAVEHDR = None
        self._play_thread = None
        self._running = False

    @property
    def active(self):
        return self._running and self._hwo is not None

    def status(self):
        if not AUDIO_ENABLED:
            return "audio off"
        if self.active:
            return f"audio on ({self.rate} Hz)"
        return "audio unavailable"

    def start(self):
        if not AUDIO_ENABLED or self._running:
            return
        self._alive = True
        self._running = True
        if sys.platform == "win32":
            self._open_winmm()
        if self._play_thread is None or not self._play_thread.is_alive():
            self._play_thread = threading.Thread(target=self._play_loop, daemon=True)
            self._play_thread.start()

    def push(self, sample):
        if not self._running:
            return
        amp = max(-1.0, min(1.0, sample * self.AUDIO_GAIN))
        with self._lock:
            self._queue.append(amp)

    def stop(self):
        self._alive = False
        self._running = False
        if self._hwo is not None and self._winmm is not None:
            try:
                self._winmm.waveOutReset(self._hwo)
            except (AttributeError, OSError):
                pass

    @staticmethod
    def _win_pump():
        if sys.platform != "win32":
            return
        try:
            user32 = ctypes.windll.user32
        except (AttributeError, OSError):
            return
        class _MSG(ctypes.Structure):
            _fields_ = [
                ("hwnd", ctypes.c_void_p),
                ("message", ctypes.c_uint),
                ("wParam", ctypes.c_size_t),
                ("lParam", ctypes.c_size_t),
                ("time", ctypes.c_uint),
                ("pt_x", ctypes.c_long),
                ("pt_y", ctypes.c_long),
            ]
        msg = _MSG()
        while user32.PeekMessageW(ctypes.byref(msg), None, 0, 0, 1):
            user32.TranslateMessage(ctypes.byref(msg))
            user32.DispatchMessageW(ctypes.byref(msg))

    def _open_winmm(self):
        if self._hwo is not None:
            return
        try:
            winmm = ctypes.windll.winmm
        except (AttributeError, OSError):
            return
        class WAVEFORMATEX(ctypes.Structure):
            _fields_ = [
                ("wFormatTag", ctypes.c_uint16),
                ("nChannels", ctypes.c_uint16),
                ("nSamplesPerSec", ctypes.c_uint32),
                ("nAvgBytesPerSec", ctypes.c_uint32),
                ("nBlockAlign", ctypes.c_uint16),
                ("wBitsPerSample", ctypes.c_uint16),
                ("cbSize", ctypes.c_uint16),
            ]
        fmt = WAVEFORMATEX(1, 1, self.rate, self.rate * 2, 2, 16, 0)
        hwo = ctypes.c_void_p()
        if winmm.waveOutOpen(ctypes.byref(hwo), 0xFFFFFFFF, ctypes.byref(fmt),
                             0, 0, 0) != 0:
            return
        self._hwo = hwo
        self._winmm = winmm
        try:
            winmm.waveOutSetVolume(self._hwo, 0xFFFFFFFF)
            winmm.waveOutRestart(self._hwo)
        except (AttributeError, OSError):
            pass
        class WAVEHDR(ctypes.Structure):
            _fields_ = [
                ("lpData", ctypes.c_char_p),
                ("dwBufferLength", ctypes.c_uint32),
                ("dwBytesRecorded", ctypes.c_uint32),
                ("dwUser", ctypes.c_size_t),
                ("dwFlags", ctypes.c_uint32),
                ("dwLoops", ctypes.c_uint32),
                ("lpNext", ctypes.c_void_p),
                ("reserved", ctypes.c_size_t),
            ]
        self._WAVEHDR = WAVEHDR
        self._pool.clear()
        self._pool_free.clear()
        self._due_at.clear()
        for i in range(self._POOL):
            buf = ctypes.create_string_buffer(self._CHUNK * 2)
            hdr = WAVEHDR()
            hdr.lpData = ctypes.cast(buf, ctypes.c_char_p)
            hdr.dwBufferLength = self._CHUNK * 2
            hdr.dwFlags = 0
            self._pool.append((buf, hdr))
            self._pool_free.add(i)

    def _release_buffer(self, idx):
        if idx in self._pool_free:
            return
        _, hdr = self._pool[idx]
        winmm = self._winmm
        if hdr.dwFlags & 0x00000002:  # WHDR_PREPARED
            winmm.waveOutUnprepareHeader(self._hwo, ctypes.byref(hdr),
                                         ctypes.sizeof(hdr))
        hdr.dwFlags = 0
        self._pool_free.add(idx)
        self._due_at.pop(idx, None)

    def _reap_done(self):
        now = time.perf_counter()
        for i in range(self._POOL):
            if i in self._pool_free:
                continue
            _, hdr = self._pool[i]
            if hdr.dwFlags & self.WHDR_DONE or now >= self._due_at.get(i, 0):
                self._release_buffer(i)

    def _play_loop(self):
        if self._hwo is None:
            while self._alive:
                with self._lock:
                    while self._queue:
                        self._queue.popleft()
                time.sleep(0.02)
            return
        winmm = self._winmm
        chunk_sec = self._CHUNK / self.rate
        while self._alive:
            self._win_pump()
            self._reap_done()
            with self._lock:
                n = len(self._queue)
            if n < self._MIN_START or not self._pool_free:
                time.sleep(0.001)
                continue
            take = min(self._CHUNK, n)
            idx = min(self._pool_free)
            self._pool_free.remove(idx)
            buf, hdr = self._pool[idx]
            with self._lock:
                samples = [self._queue.popleft() for _ in range(take)]
            pcm = bytearray(self._CHUNK * 2)
            for i, s in enumerate(samples):
                val = int(max(-32768, min(32767, s * 32767)))
                pcm[i * 2] = val & 0xFF
                pcm[i * 2 + 1] = (val >> 8) & 0xFF
            ctypes.memmove(buf, bytes(pcm), self._CHUNK * 2)
            hdr.dwBufferLength = self._CHUNK * 2
            hdr.dwFlags = 0
            if winmm.waveOutPrepareHeader(self._hwo, ctypes.byref(hdr),
                                          ctypes.sizeof(hdr)) != 0:
                self._pool_free.add(idx)
                time.sleep(0.001)
                continue
            if winmm.waveOutWrite(self._hwo, ctypes.byref(hdr),
                                  ctypes.sizeof(hdr)) != 0:
                self._release_buffer(idx)
                time.sleep(0.001)
                continue
            self._due_at[idx] = time.perf_counter() + chunk_sec + 0.005


class AudioStream:
    """Low-latency mono PCM using only native OS APIs and ctypes."""

    _CHUNK = 512
    _POOL = 6
    _MIN_START = 768
    _MAX_LATENCY = SAMPLE_RATE // 5
    WHDR_DONE = 0x00000001
    WHDR_PREPARED = 0x00000002
    AUDIO_GAIN = 2.0

    def __init__(self, rate=SAMPLE_RATE):
        self.rate = rate
        self._queue = deque(maxlen=rate // 2)
        self._lock = threading.Lock()
        self._alive = False
        self._running = False
        self._backend = "none"
        self._play_thread = None
        self._winmm = None
        self._hwo = None
        self._pool = []
        self._pool_free = set()
        self._coreaudio = None
        self._audio_queue = None
        self._coreaudio_callback = None
        self._core_buffers = []
        self._alsa = None
        self._alsa_pcm = None
        self._alsa_error_handler = None

    @property
    def active(self):
        return self._running and self._backend != "none"

    def status(self):
        if not AUDIO_ENABLED:
            return "audio off"
        if self.active:
            names = {"winmm": "WinMM", "coreaudio": "CoreAudio", "alsa": "ALSA"}
            return f"audio on ({names.get(self._backend, self._backend)}, {self.rate} Hz)"
        return "audio unavailable"

    def start(self):
        if not AUDIO_ENABLED or self.active:
            return
        self._alive = True
        if sys.platform == "win32":
            self._open_winmm()
        elif sys.platform == "darwin":
            self._open_coreaudio()
        elif sys.platform.startswith("linux"):
            self._open_alsa()
        if self._backend == "none":
            self._alive = False
            return
        self._running = True
        if self._backend in ("winmm", "alsa"):
            self._play_thread = threading.Thread(
                target=self._play_loop, name="luigines-audio", daemon=True)
            self._play_thread.start()

    def push(self, sample):
        if not self.active:
            return
        amp = max(-1.0, min(1.0, sample * self.AUDIO_GAIN))
        with self._lock:
            self._queue.append(amp)

    def _take_pcm(self, frames):
        with self._lock:
            if len(self._queue) > self._MAX_LATENCY:
                trim_to = self._MIN_START + self._CHUNK
                for _ in range(len(self._queue) - trim_to):
                    self._queue.popleft()
            take = min(frames, len(self._queue))
            samples = [self._queue.popleft() for _ in range(take)]
        pcm = bytearray(frames * 2)
        for i, sample in enumerate(samples):
            value = int(max(-32768, min(32767, sample * 32767.0)))
            pcm[i * 2] = value & 0xFF
            pcm[i * 2 + 1] = (value >> 8) & 0xFF
        return bytes(pcm)

    def stop(self):
        self._alive = False
        self._running = False
        if self._backend == "winmm" and self._winmm is not None and self._hwo:
            self._winmm.waveOutReset(self._hwo)
        elif self._backend == "alsa" and self._alsa is not None and self._alsa_pcm:
            self._alsa.snd_pcm_drop(self._alsa_pcm)
        elif self._backend == "coreaudio" and self._coreaudio is not None and self._audio_queue:
            self._coreaudio.AudioQueueStop(self._audio_queue, True)
        if (self._play_thread is not None
                and self._play_thread is not threading.current_thread()):
            self._play_thread.join(timeout=0.5)
        if self._backend == "winmm":
            self._close_winmm()
        elif self._backend == "coreaudio":
            self._close_coreaudio()
        elif self._backend == "alsa":
            self._close_alsa()
        with self._lock:
            self._queue.clear()
        self._backend = "none"

    # -- Windows: waveOut -------------------------------------------------

    def _open_winmm(self):
        try:
            winmm = ctypes.windll.winmm
        except (AttributeError, OSError):
            return

        class WAVEFORMATEX(ctypes.Structure):
            _fields_ = [
                ("wFormatTag", ctypes.c_uint16), ("nChannels", ctypes.c_uint16),
                ("nSamplesPerSec", ctypes.c_uint32),
                ("nAvgBytesPerSec", ctypes.c_uint32),
                ("nBlockAlign", ctypes.c_uint16), ("wBitsPerSample", ctypes.c_uint16),
                ("cbSize", ctypes.c_uint16),
            ]

        class WAVEHDR(ctypes.Structure):
            _fields_ = [
                ("lpData", ctypes.c_void_p), ("dwBufferLength", ctypes.c_uint32),
                ("dwBytesRecorded", ctypes.c_uint32), ("dwUser", ctypes.c_size_t),
                ("dwFlags", ctypes.c_uint32), ("dwLoops", ctypes.c_uint32),
                ("lpNext", ctypes.c_void_p), ("reserved", ctypes.c_size_t),
            ]

        winmm.waveOutOpen.argtypes = [ctypes.POINTER(ctypes.c_void_p), ctypes.c_uint,
                                      ctypes.POINTER(WAVEFORMATEX), ctypes.c_void_p,
                                      ctypes.c_void_p, ctypes.c_uint]
        winmm.waveOutPrepareHeader.argtypes = [
            ctypes.c_void_p, ctypes.POINTER(WAVEHDR), ctypes.c_uint]
        winmm.waveOutWrite.argtypes = [
            ctypes.c_void_p, ctypes.POINTER(WAVEHDR), ctypes.c_uint]
        winmm.waveOutUnprepareHeader.argtypes = [
            ctypes.c_void_p, ctypes.POINTER(WAVEHDR), ctypes.c_uint]
        winmm.waveOutReset.argtypes = [ctypes.c_void_p]
        winmm.waveOutClose.argtypes = [ctypes.c_void_p]
        fmt = WAVEFORMATEX(1, 1, self.rate, self.rate * 2, 2, 16, 0)
        handle = ctypes.c_void_p()
        if winmm.waveOutOpen(ctypes.byref(handle), 0xFFFFFFFF, ctypes.byref(fmt),
                             None, None, 0) != 0:
            return
        self._winmm = winmm
        self._hwo = handle
        self._pool = []
        self._pool_free = set(range(self._POOL))
        for _ in range(self._POOL):
            buf = ctypes.create_string_buffer(self._CHUNK * 2)
            hdr = WAVEHDR(ctypes.cast(buf, ctypes.c_void_p), self._CHUNK * 2,
                          0, 0, 0, 0, None, 0)
            self._pool.append((buf, hdr))
        self._backend = "winmm"

    def _release_winmm_buffer(self, idx):
        if idx in self._pool_free:
            return
        _, hdr = self._pool[idx]
        if hdr.dwFlags & self.WHDR_PREPARED:
            self._winmm.waveOutUnprepareHeader(
                self._hwo, ctypes.byref(hdr), ctypes.sizeof(hdr))
        hdr.dwFlags = 0
        self._pool_free.add(idx)

    def _reap_winmm(self):
        for idx, (_, hdr) in enumerate(self._pool):
            if idx not in self._pool_free and hdr.dwFlags & self.WHDR_DONE:
                self._release_winmm_buffer(idx)

    def _winmm_loop(self):
        while self._alive:
            self._reap_winmm()
            with self._lock:
                ready = len(self._queue) >= self._MIN_START
            if not ready or not self._pool_free:
                time.sleep(0.001)
                continue
            idx = min(self._pool_free)
            self._pool_free.remove(idx)
            buf, hdr = self._pool[idx]
            pcm = self._take_pcm(self._CHUNK)
            ctypes.memmove(buf, pcm, len(pcm))
            hdr.dwBufferLength = len(pcm)
            hdr.dwFlags = 0
            if self._winmm.waveOutPrepareHeader(
                    self._hwo, ctypes.byref(hdr), ctypes.sizeof(hdr)) != 0:
                self._pool_free.add(idx)
                continue
            if self._winmm.waveOutWrite(
                    self._hwo, ctypes.byref(hdr), ctypes.sizeof(hdr)) != 0:
                self._release_winmm_buffer(idx)

    def _close_winmm(self):
        if self._winmm is None or not self._hwo:
            return
        self._winmm.waveOutReset(self._hwo)
        for idx in range(len(self._pool)):
            self._release_winmm_buffer(idx)
        self._winmm.waveOutClose(self._hwo)
        self._hwo = None
        self._winmm = None
        self._pool.clear()

    # -- macOS: AudioQueue ------------------------------------------------

    def _open_coreaudio(self):
        try:
            audio = ctypes.CDLL(
                "/System/Library/Frameworks/AudioToolbox.framework/AudioToolbox")
        except OSError:
            return

        class AudioStreamBasicDescription(ctypes.Structure):
            _fields_ = [
                ("mSampleRate", ctypes.c_double), ("mFormatID", ctypes.c_uint32),
                ("mFormatFlags", ctypes.c_uint32), ("mBytesPerPacket", ctypes.c_uint32),
                ("mFramesPerPacket", ctypes.c_uint32), ("mBytesPerFrame", ctypes.c_uint32),
                ("mChannelsPerFrame", ctypes.c_uint32), ("mBitsPerChannel", ctypes.c_uint32),
                ("mReserved", ctypes.c_uint32),
            ]

        class AudioQueueBuffer(ctypes.Structure):
            _fields_ = [
                ("mAudioDataBytesCapacity", ctypes.c_uint32),
                ("mAudioData", ctypes.c_void_p),
                ("mAudioDataByteSize", ctypes.c_uint32),
                ("mUserData", ctypes.c_void_p),
                ("mPacketDescriptionCapacity", ctypes.c_uint32),
                ("mPacketDescriptions", ctypes.c_void_p),
            ]

        buffer_ref = ctypes.POINTER(AudioQueueBuffer)
        callback_type = ctypes.CFUNCTYPE(None, ctypes.c_void_p, ctypes.c_void_p, buffer_ref)
        audio.AudioQueueNewOutput.argtypes = [
            ctypes.POINTER(AudioStreamBasicDescription), callback_type,
            ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_uint32,
            ctypes.POINTER(ctypes.c_void_p),
        ]
        audio.AudioQueueAllocateBuffer.argtypes = [
            ctypes.c_void_p, ctypes.c_uint32, ctypes.POINTER(buffer_ref)]
        audio.AudioQueueEnqueueBuffer.argtypes = [
            ctypes.c_void_p, buffer_ref, ctypes.c_uint32, ctypes.c_void_p]
        audio.AudioQueueStart.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
        audio.AudioQueueStop.argtypes = [ctypes.c_void_p, ctypes.c_ubyte]
        audio.AudioQueueDispose.argtypes = [ctypes.c_void_p, ctypes.c_ubyte]

        def fill_buffer(_user, queue, buffer):
            if not self._alive:
                return
            pcm = self._take_pcm(self._CHUNK)
            ctypes.memmove(buffer.contents.mAudioData, pcm, len(pcm))
            buffer.contents.mAudioDataByteSize = len(pcm)
            audio.AudioQueueEnqueueBuffer(queue, buffer, 0, None)

        callback = callback_type(fill_buffer)
        # 'lpcm', signed integer, packed, native-endian mono 16-bit.
        fmt = AudioStreamBasicDescription(
            float(self.rate), 0x6C70636D, 0x0C, 2, 1, 2, 1, 16, 0)
        queue = ctypes.c_void_p()
        if audio.AudioQueueNewOutput(
                ctypes.byref(fmt), callback, None, None, None, 0,
                ctypes.byref(queue)) != 0:
            return
        self._coreaudio = audio
        self._audio_queue = queue
        self._coreaudio_callback = callback
        self._core_buffers = []
        for _ in range(self._POOL):
            buffer = buffer_ref()
            if audio.AudioQueueAllocateBuffer(
                    queue, self._CHUNK * 2, ctypes.byref(buffer)) != 0:
                self._close_coreaudio()
                return
            self._core_buffers.append(buffer)
            fill_buffer(None, queue, buffer)
        if audio.AudioQueueStart(queue, None) != 0:
            self._close_coreaudio()
            return
        self._backend = "coreaudio"

    def _close_coreaudio(self):
        if self._coreaudio is not None and self._audio_queue:
            self._coreaudio.AudioQueueStop(self._audio_queue, True)
            self._coreaudio.AudioQueueDispose(self._audio_queue, True)
        self._audio_queue = None
        self._coreaudio = None
        self._coreaudio_callback = None
        self._core_buffers.clear()

    # -- Linux: ALSA ------------------------------------------------------

    def _open_alsa(self):
        name = ctypes.util.find_library("asound") or "libasound.so.2"
        try:
            alsa = ctypes.CDLL(name)
        except OSError:
            return
        error_type = ctypes.CFUNCTYPE(
            None, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p,
            ctypes.c_int, ctypes.c_char_p)
        self._alsa_error_handler = error_type(lambda *_args: None)
        try:
            alsa.snd_lib_error_set_handler(self._alsa_error_handler)
        except AttributeError:
            pass
        alsa.snd_pcm_open.argtypes = [ctypes.POINTER(ctypes.c_void_p), ctypes.c_char_p,
                                      ctypes.c_int, ctypes.c_int]
        alsa.snd_pcm_set_params.argtypes = [ctypes.c_void_p, ctypes.c_int,
                                            ctypes.c_int, ctypes.c_uint,
                                            ctypes.c_uint, ctypes.c_int,
                                            ctypes.c_uint]
        alsa.snd_pcm_writei.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_ulong]
        alsa.snd_pcm_writei.restype = ctypes.c_long
        alsa.snd_pcm_recover.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_int]
        alsa.snd_pcm_drop.argtypes = [ctypes.c_void_p]
        alsa.snd_pcm_close.argtypes = [ctypes.c_void_p]
        pcm = ctypes.c_void_p()
        if alsa.snd_pcm_open(ctypes.byref(pcm), b"default", 0, 0) < 0:
            return
        # S16_LE=2, RW_INTERLEAVED=3, mono, 80 ms hardware latency.
        if alsa.snd_pcm_set_params(pcm, 2, 3, 1, self.rate, 1, 80000) < 0:
            alsa.snd_pcm_close(pcm)
            return
        self._alsa = alsa
        self._alsa_pcm = pcm
        self._backend = "alsa"

    def _alsa_loop(self):
        while self._alive:
            with self._lock:
                ready = len(self._queue) >= self._MIN_START
            if not ready:
                time.sleep(0.001)
                continue
            pcm = self._take_pcm(self._CHUNK)
            data = ctypes.create_string_buffer(pcm)
            result = self._alsa.snd_pcm_writei(
                self._alsa_pcm, ctypes.cast(data, ctypes.c_void_p), self._CHUNK)
            if result < 0:
                self._alsa.snd_pcm_recover(self._alsa_pcm, int(result), 1)

    def _close_alsa(self):
        if self._alsa is not None and self._alsa_pcm:
            self._alsa.snd_pcm_drop(self._alsa_pcm)
            self._alsa.snd_pcm_close(self._alsa_pcm)
        self._alsa_pcm = None
        self._alsa = None
        self._alsa_error_handler = None

    def _play_loop(self):
        if self._backend == "winmm":
            self._winmm_loop()
        elif self._backend == "alsa":
            self._alsa_loop()


# =============================================================================
#  Controller
# =============================================================================

class Controller:
    BTN_A      = 0x01
    BTN_B      = 0x02
    BTN_SELECT = 0x04
    BTN_START  = 0x08
    BTN_UP     = 0x10
    BTN_DOWN   = 0x20
    BTN_LEFT   = 0x40
    BTN_RIGHT  = 0x80
    def __init__(self):
        self.state = 0
        self.shift = 0
        self.strobe = False
    def set_strobe(self, val):
        old = self.strobe
        self.strobe = bool(val & 1)
        if old and not self.strobe:
            self.shift = self.state
    def read(self):
        if self.strobe:
            return self.state & 1
        v = self.shift & 1
        self.shift = (self.shift >> 1) | 0x80
        return v


# =============================================================================
#  CPU bus
# =============================================================================

class Bus:
    def __init__(self, mapper, ppu, apu, pad1, pad2):
        self.ram = bytearray(2048)
        self.mapper = mapper
        self.ppu = ppu
        self.apu = apu
        self.pad1 = pad1
        self.pad2 = pad2
        self.dma_stall = 0
        self.cpu = None

    def read(self, addr):
        addr &= 0xFFFF
        if addr < 0x2000:
            return self.ram[addr & 0x07FF]
        if addr < 0x4000:
            return self.ppu.reg_read(addr & 7)
        if addr == 0x4015:
            return self.apu.read_status()
        if addr == 0x4016:
            return 0x40 | self.pad1.read()
        if addr == 0x4017:
            return 0x40 | self.pad2.read()
        if addr < 0x4018:
            return 0
        return self.mapper.cpu_read(addr)

    def write(self, addr, val):
        addr &= 0xFFFF
        val &= 0xFF
        if addr < 0x2000:
            self.ram[addr & 0x07FF] = val
        elif addr < 0x4000:
            self.ppu.reg_write(addr & 7, val)
        elif addr == 0x4014:
            page = val << 8
            data = bytes(self.read(page + i) for i in range(256))
            self.ppu.oam_dma_write(data)
            self.dma_stall += 513
        elif addr == 0x4016:
            self.pad1.set_strobe(val)
            self.pad2.set_strobe(val)
        elif addr < 0x4018:
            self.apu.write(addr, val)
        else:
            self.mapper.cpu_write(addr, val)


# =============================================================================
#  6502 CPU
# =============================================================================

class CPU:
    FLAG_C = 0x01
    FLAG_Z = 0x02
    FLAG_I = 0x04
    FLAG_D = 0x08
    FLAG_B = 0x10
    FLAG_U = 0x20
    FLAG_V = 0x40
    FLAG_N = 0x80

    def __init__(self, bus):
        self.bus = bus
        bus.cpu = self
        self.a = 0
        self.x = 0
        self.y = 0
        self.sp = 0xFD
        self.p = 0x24
        self.pc = 0
        self.cycles = 0
        self.pending_nmi = False
        self.pending_irq = False
        self.jammed = False
        self._mapper = bus.mapper
        self._build_table()

    def reset(self):
        lo = self.bus.read(0xFFFC)
        hi = self.bus.read(0xFFFD)
        self.pc = (hi << 8) | lo
        self.sp = 0xFD
        self.p = 0x24
        self.cycles = 7
        self.jammed = False

    def _read(self, addr):
        addr &= 0xFFFF
        if addr >= 0x8000:
            return self.bus.mapper.cpu_read(addr) & 0xFF
        return self.bus.read(addr) & 0xFF
    def _write(self, addr, val): self.bus.write(addr, val & 0xFF)
    def _read16(self, addr):
        return self._read(addr) | (self._read((addr + 1) & 0xFFFF) << 8)
    def _read16_bug(self, addr):
        a2 = (addr & 0xFF00) | ((addr + 1) & 0xFF)
        return self._read(addr) | (self._read(a2) << 8)
    def _push(self, val):
        self._write(0x100 | self.sp, val)
        self.sp = (self.sp - 1) & 0xFF
    def _pull(self):
        self.sp = (self.sp + 1) & 0xFF
        return self._read(0x100 | self.sp)
    def _push16(self, val):
        self._push((val >> 8) & 0xFF)
        self._push(val & 0xFF)
    def _pull16(self):
        lo = self._pull()
        hi = self._pull()
        return (hi << 8) | lo
    def _set_zn(self, v):
        v &= 0xFF
        self.p = (self.p & ~(self.FLAG_Z | self.FLAG_N))
        if v == 0: self.p |= self.FLAG_Z
        if v & 0x80: self.p |= self.FLAG_N

    def nmi(self): self.pending_nmi = True

    def _do_nmi(self):
        self._push16(self.pc)
        self._push((self.p | 0x20) & ~self.FLAG_B)
        self.p |= self.FLAG_I
        self.pc = self._read(0xFFFA) | (self._read(0xFFFB) << 8)
        self.cycles += 7

    def _do_irq(self):
        self._push16(self.pc)
        self._push((self.p | 0x20) & ~self.FLAG_B)
        self.p |= self.FLAG_I
        self.pc = self._read(0xFFFE) | (self._read(0xFFFF) << 8)
        self.cycles += 7

    # Addressing modes
    def _am_imm(self):
        a = self.pc; self.pc = (self.pc + 1) & 0xFFFF; return a, 0
    def _am_zp(self):
        a = self._read(self.pc); self.pc = (self.pc + 1) & 0xFFFF; return a, 0
    def _am_zpx(self):
        a = (self._read(self.pc) + self.x) & 0xFF
        self.pc = (self.pc + 1) & 0xFFFF; return a, 0
    def _am_zpy(self):
        a = (self._read(self.pc) + self.y) & 0xFF
        self.pc = (self.pc + 1) & 0xFFFF; return a, 0
    def _am_abs(self):
        a = self._read16(self.pc); self.pc = (self.pc + 2) & 0xFFFF; return a, 0
    def _am_absx(self, write=False):
        base = self._read16(self.pc); self.pc = (self.pc + 2) & 0xFFFF
        a = (base + self.x) & 0xFFFF
        extra = 0 if write else (1 if (base & 0xFF00) != (a & 0xFF00) else 0)
        return a, extra
    def _am_absy(self, write=False):
        base = self._read16(self.pc); self.pc = (self.pc + 2) & 0xFFFF
        a = (base + self.y) & 0xFFFF
        extra = 0 if write else (1 if (base & 0xFF00) != (a & 0xFF00) else 0)
        return a, extra
    def _am_ind(self):
        ptr = self._read16(self.pc); self.pc = (self.pc + 2) & 0xFFFF
        return self._read16_bug(ptr), 0
    def _am_indx(self):
        zp = (self._read(self.pc) + self.x) & 0xFF
        self.pc = (self.pc + 1) & 0xFFFF
        return self._read(zp) | (self._read((zp + 1) & 0xFF) << 8), 0
    def _am_indy(self, write=False):
        zp = self._read(self.pc); self.pc = (self.pc + 1) & 0xFFFF
        base = self._read(zp) | (self._read((zp + 1) & 0xFF) << 8)
        a = (base + self.y) & 0xFFFF
        extra = 0 if write else (1 if (base & 0xFF00) != (a & 0xFF00) else 0)
        return a, extra
    def _am_rel(self):
        d = self._read(self.pc); self.pc = (self.pc + 1) & 0xFFFF
        if d & 0x80: d -= 0x100
        return (self.pc + d) & 0xFFFF, 0

    # Ops
    def _adc_val(self, m):
        c = self.p & 1
        r = self.a + m + c
        v = (~(self.a ^ m) & (self.a ^ r)) & 0x80
        self.p = (self.p & ~(self.FLAG_C | self.FLAG_V)) | (1 if r > 0xFF else 0) | (self.FLAG_V if v else 0)
        self.a = r & 0xFF
        self._set_zn(self.a)
    def _op_adc(self, a): self._adc_val(self._read(a))
    def _op_sbc(self, a): self._adc_val(self._read(a) ^ 0xFF)
    def _op_and(self, a): self.a &= self._read(a); self._set_zn(self.a)
    def _op_ora(self, a): self.a |= self._read(a); self._set_zn(self.a)
    def _op_eor(self, a): self.a ^= self._read(a); self._set_zn(self.a)
    def _op_asl_a(self):
        self.p = (self.p & ~1) | ((self.a >> 7) & 1)
        self.a = (self.a << 1) & 0xFF; self._set_zn(self.a)
    def _op_asl(self, a):
        m = self._read(a); self._write(a, m)
        self.p = (self.p & ~1) | ((m >> 7) & 1)
        m = (m << 1) & 0xFF; self._write(a, m); self._set_zn(m)
    def _op_lsr_a(self):
        self.p = (self.p & ~1) | (self.a & 1); self.a >>= 1; self._set_zn(self.a)
    def _op_lsr(self, a):
        m = self._read(a); self._write(a, m)
        self.p = (self.p & ~1) | (m & 1); m >>= 1; self._write(a, m); self._set_zn(m)
    def _op_rol_a(self):
        c = self.p & 1
        self.p = (self.p & ~1) | ((self.a >> 7) & 1)
        self.a = ((self.a << 1) | c) & 0xFF; self._set_zn(self.a)
    def _op_rol(self, a):
        m = self._read(a); self._write(a, m); c = self.p & 1
        self.p = (self.p & ~1) | ((m >> 7) & 1)
        m = ((m << 1) | c) & 0xFF; self._write(a, m); self._set_zn(m)
    def _op_ror_a(self):
        c = (self.p & 1) << 7
        self.p = (self.p & ~1) | (self.a & 1)
        self.a = (self.a >> 1) | c; self._set_zn(self.a)
    def _op_ror(self, a):
        m = self._read(a); self._write(a, m); c = (self.p & 1) << 7
        self.p = (self.p & ~1) | (m & 1)
        m = (m >> 1) | c; self._write(a, m); self._set_zn(m)
    def _op_bit(self, a):
        m = self._read(a); r = self.a & m
        self.p = (self.p & ~(self.FLAG_Z | self.FLAG_N | self.FLAG_V))
        if r == 0: self.p |= self.FLAG_Z
        self.p |= (m & 0xC0)
    def _op_cmp(self, reg, a):
        m = self._read(a); r = reg - m
        self.p = (self.p & ~1) | (1 if reg >= m else 0)
        self._set_zn(r & 0xFF)
    def _branch(self, cond, target):
        if not cond: return 0
        extra = 2 if (target & 0xFF00) != (self.pc & 0xFF00) else 1
        self.pc = target
        return extra

    def _build_table(self):
        T = [None] * 256
        def op(c, fn, cy): T[c] = (fn, cy)

        op(0x69, lambda: (self._op_adc(self._am_imm()[0]), 0)[1], 2)
        op(0x65, lambda: (self._op_adc(self._am_zp()[0]), 0)[1], 3)
        op(0x75, lambda: (self._op_adc(self._am_zpx()[0]), 0)[1], 4)
        op(0x6D, lambda: (self._op_adc(self._am_abs()[0]), 0)[1], 4)
        op(0x7D, lambda: (lambda r: (self._op_adc(r[0]), r[1])[1])(self._am_absx()), 4)
        op(0x79, lambda: (lambda r: (self._op_adc(r[0]), r[1])[1])(self._am_absy()), 4)
        op(0x61, lambda: (self._op_adc(self._am_indx()[0]), 0)[1], 6)
        op(0x71, lambda: (lambda r: (self._op_adc(r[0]), r[1])[1])(self._am_indy()), 5)
        op(0xE9, lambda: (self._op_sbc(self._am_imm()[0]), 0)[1], 2)
        op(0xEB, lambda: (self._op_sbc(self._am_imm()[0]), 0)[1], 2)
        op(0xE5, lambda: (self._op_sbc(self._am_zp()[0]), 0)[1], 3)
        op(0xF5, lambda: (self._op_sbc(self._am_zpx()[0]), 0)[1], 4)
        op(0xED, lambda: (self._op_sbc(self._am_abs()[0]), 0)[1], 4)
        op(0xFD, lambda: (lambda r: (self._op_sbc(r[0]), r[1])[1])(self._am_absx()), 4)
        op(0xF9, lambda: (lambda r: (self._op_sbc(r[0]), r[1])[1])(self._am_absy()), 4)
        op(0xE1, lambda: (self._op_sbc(self._am_indx()[0]), 0)[1], 6)
        op(0xF1, lambda: (lambda r: (self._op_sbc(r[0]), r[1])[1])(self._am_indy()), 5)
        op(0x29, lambda: (self._op_and(self._am_imm()[0]), 0)[1], 2)
        op(0x25, lambda: (self._op_and(self._am_zp()[0]), 0)[1], 3)
        op(0x35, lambda: (self._op_and(self._am_zpx()[0]), 0)[1], 4)
        op(0x2D, lambda: (self._op_and(self._am_abs()[0]), 0)[1], 4)
        op(0x3D, lambda: (lambda r: (self._op_and(r[0]), r[1])[1])(self._am_absx()), 4)
        op(0x39, lambda: (lambda r: (self._op_and(r[0]), r[1])[1])(self._am_absy()), 4)
        op(0x21, lambda: (self._op_and(self._am_indx()[0]), 0)[1], 6)
        op(0x31, lambda: (lambda r: (self._op_and(r[0]), r[1])[1])(self._am_indy()), 5)
        op(0x09, lambda: (self._op_ora(self._am_imm()[0]), 0)[1], 2)
        op(0x05, lambda: (self._op_ora(self._am_zp()[0]), 0)[1], 3)
        op(0x15, lambda: (self._op_ora(self._am_zpx()[0]), 0)[1], 4)
        op(0x0D, lambda: (self._op_ora(self._am_abs()[0]), 0)[1], 4)
        op(0x1D, lambda: (lambda r: (self._op_ora(r[0]), r[1])[1])(self._am_absx()), 4)
        op(0x19, lambda: (lambda r: (self._op_ora(r[0]), r[1])[1])(self._am_absy()), 4)
        op(0x01, lambda: (self._op_ora(self._am_indx()[0]), 0)[1], 6)
        op(0x11, lambda: (lambda r: (self._op_ora(r[0]), r[1])[1])(self._am_indy()), 5)
        op(0x49, lambda: (self._op_eor(self._am_imm()[0]), 0)[1], 2)
        op(0x45, lambda: (self._op_eor(self._am_zp()[0]), 0)[1], 3)
        op(0x55, lambda: (self._op_eor(self._am_zpx()[0]), 0)[1], 4)
        op(0x4D, lambda: (self._op_eor(self._am_abs()[0]), 0)[1], 4)
        op(0x5D, lambda: (lambda r: (self._op_eor(r[0]), r[1])[1])(self._am_absx()), 4)
        op(0x59, lambda: (lambda r: (self._op_eor(r[0]), r[1])[1])(self._am_absy()), 4)
        op(0x41, lambda: (self._op_eor(self._am_indx()[0]), 0)[1], 6)
        op(0x51, lambda: (lambda r: (self._op_eor(r[0]), r[1])[1])(self._am_indy()), 5)
        op(0x0A, lambda: (self._op_asl_a(), 0)[1], 2)
        op(0x06, lambda: (self._op_asl(self._am_zp()[0]), 0)[1], 5)
        op(0x16, lambda: (self._op_asl(self._am_zpx()[0]), 0)[1], 6)
        op(0x0E, lambda: (self._op_asl(self._am_abs()[0]), 0)[1], 6)
        op(0x1E, lambda: (self._op_asl(self._am_absx(True)[0]), 0)[1], 7)
        op(0x4A, lambda: (self._op_lsr_a(), 0)[1], 2)
        op(0x46, lambda: (self._op_lsr(self._am_zp()[0]), 0)[1], 5)
        op(0x56, lambda: (self._op_lsr(self._am_zpx()[0]), 0)[1], 6)
        op(0x4E, lambda: (self._op_lsr(self._am_abs()[0]), 0)[1], 6)
        op(0x5E, lambda: (self._op_lsr(self._am_absx(True)[0]), 0)[1], 7)
        op(0x2A, lambda: (self._op_rol_a(), 0)[1], 2)
        op(0x26, lambda: (self._op_rol(self._am_zp()[0]), 0)[1], 5)
        op(0x36, lambda: (self._op_rol(self._am_zpx()[0]), 0)[1], 6)
        op(0x2E, lambda: (self._op_rol(self._am_abs()[0]), 0)[1], 6)
        op(0x3E, lambda: (self._op_rol(self._am_absx(True)[0]), 0)[1], 7)
        op(0x6A, lambda: (self._op_ror_a(), 0)[1], 2)
        op(0x66, lambda: (self._op_ror(self._am_zp()[0]), 0)[1], 5)
        op(0x76, lambda: (self._op_ror(self._am_zpx()[0]), 0)[1], 6)
        op(0x6E, lambda: (self._op_ror(self._am_abs()[0]), 0)[1], 6)
        op(0x7E, lambda: (self._op_ror(self._am_absx(True)[0]), 0)[1], 7)
        op(0x24, lambda: (self._op_bit(self._am_zp()[0]), 0)[1], 3)
        op(0x2C, lambda: (self._op_bit(self._am_abs()[0]), 0)[1], 4)

        def _lda(a): self.a = self._read(a); self._set_zn(self.a)
        def _ldx(a): self.x = self._read(a); self._set_zn(self.x)
        def _ldy(a): self.y = self._read(a); self._set_zn(self.y)
        op(0xA9, lambda: (_lda(self._am_imm()[0]), 0)[1], 2)
        op(0xA5, lambda: (_lda(self._am_zp()[0]), 0)[1], 3)
        op(0xB5, lambda: (_lda(self._am_zpx()[0]), 0)[1], 4)
        op(0xAD, lambda: (_lda(self._am_abs()[0]), 0)[1], 4)
        op(0xBD, lambda: (lambda r: (_lda(r[0]), r[1])[1])(self._am_absx()), 4)
        op(0xB9, lambda: (lambda r: (_lda(r[0]), r[1])[1])(self._am_absy()), 4)
        op(0xA1, lambda: (_lda(self._am_indx()[0]), 0)[1], 6)
        op(0xB1, lambda: (lambda r: (_lda(r[0]), r[1])[1])(self._am_indy()), 5)
        op(0xA2, lambda: (_ldx(self._am_imm()[0]), 0)[1], 2)
        op(0xA6, lambda: (_ldx(self._am_zp()[0]), 0)[1], 3)
        op(0xB6, lambda: (_ldx(self._am_zpy()[0]), 0)[1], 4)
        op(0xAE, lambda: (_ldx(self._am_abs()[0]), 0)[1], 4)
        op(0xBE, lambda: (lambda r: (_ldx(r[0]), r[1])[1])(self._am_absy()), 4)
        op(0xA0, lambda: (_ldy(self._am_imm()[0]), 0)[1], 2)
        op(0xA4, lambda: (_ldy(self._am_zp()[0]), 0)[1], 3)
        op(0xB4, lambda: (_ldy(self._am_zpx()[0]), 0)[1], 4)
        op(0xAC, lambda: (_ldy(self._am_abs()[0]), 0)[1], 4)
        op(0xBC, lambda: (lambda r: (_ldy(r[0]), r[1])[1])(self._am_absx()), 4)
        op(0x85, lambda: (self._write(self._am_zp()[0], self.a), 0)[1], 3)
        op(0x95, lambda: (self._write(self._am_zpx()[0], self.a), 0)[1], 4)
        op(0x8D, lambda: (self._write(self._am_abs()[0], self.a), 0)[1], 4)
        op(0x9D, lambda: (self._write(self._am_absx(True)[0], self.a), 0)[1], 5)
        op(0x99, lambda: (self._write(self._am_absy(True)[0], self.a), 0)[1], 5)
        op(0x81, lambda: (self._write(self._am_indx()[0], self.a), 0)[1], 6)
        op(0x91, lambda: (self._write(self._am_indy(True)[0], self.a), 0)[1], 6)
        op(0x86, lambda: (self._write(self._am_zp()[0], self.x), 0)[1], 3)
        op(0x96, lambda: (self._write(self._am_zpy()[0], self.x), 0)[1], 4)
        op(0x8E, lambda: (self._write(self._am_abs()[0], self.x), 0)[1], 4)
        op(0x84, lambda: (self._write(self._am_zp()[0], self.y), 0)[1], 3)
        op(0x94, lambda: (self._write(self._am_zpx()[0], self.y), 0)[1], 4)
        op(0x8C, lambda: (self._write(self._am_abs()[0], self.y), 0)[1], 4)

        def _tax(): self.x = self.a; self._set_zn(self.x)
        def _tay(): self.y = self.a; self._set_zn(self.y)
        def _txa(): self.a = self.x; self._set_zn(self.a)
        def _tya(): self.a = self.y; self._set_zn(self.a)
        def _tsx(): self.x = self.sp; self._set_zn(self.x)
        def _txs(): self.sp = self.x
        op(0xAA, lambda: (_tax(), 0)[1], 2)
        op(0xA8, lambda: (_tay(), 0)[1], 2)
        op(0x8A, lambda: (_txa(), 0)[1], 2)
        op(0x98, lambda: (_tya(), 0)[1], 2)
        op(0xBA, lambda: (_tsx(), 0)[1], 2)
        op(0x9A, lambda: (_txs(), 0)[1], 2)

        op(0x48, lambda: (self._push(self.a), 0)[1], 3)
        op(0x08, lambda: (self._push(self.p | 0x30), 0)[1], 3)
        def _pla():
            self.a = self._pull(); self._set_zn(self.a)
        op(0x68, lambda: (_pla(), 0)[1], 4)
        def _plp(): self.p = (self._pull() & ~0x10) | 0x20
        op(0x28, lambda: (_plp(), 0)[1], 4)

        def _inc(a):
            m = self._read(a); self._write(a, m)
            m = (m + 1) & 0xFF; self._write(a, m); self._set_zn(m)
        def _dec(a):
            m = self._read(a); self._write(a, m)
            m = (m - 1) & 0xFF; self._write(a, m); self._set_zn(m)
        op(0xE6, lambda: (_inc(self._am_zp()[0]), 0)[1], 5)
        op(0xF6, lambda: (_inc(self._am_zpx()[0]), 0)[1], 6)
        op(0xEE, lambda: (_inc(self._am_abs()[0]), 0)[1], 6)
        op(0xFE, lambda: (_inc(self._am_absx(True)[0]), 0)[1], 7)
        op(0xC6, lambda: (_dec(self._am_zp()[0]), 0)[1], 5)
        op(0xD6, lambda: (_dec(self._am_zpx()[0]), 0)[1], 6)
        op(0xCE, lambda: (_dec(self._am_abs()[0]), 0)[1], 6)
        op(0xDE, lambda: (_dec(self._am_absx(True)[0]), 0)[1], 7)
        def _inx(): self.x = (self.x + 1) & 0xFF; self._set_zn(self.x)
        def _dex(): self.x = (self.x - 1) & 0xFF; self._set_zn(self.x)
        def _iny(): self.y = (self.y + 1) & 0xFF; self._set_zn(self.y)
        def _dey(): self.y = (self.y - 1) & 0xFF; self._set_zn(self.y)
        op(0xE8, lambda: (_inx(), 0)[1], 2)
        op(0xCA, lambda: (_dex(), 0)[1], 2)
        op(0xC8, lambda: (_iny(), 0)[1], 2)
        op(0x88, lambda: (_dey(), 0)[1], 2)

        op(0xC9, lambda: (self._op_cmp(self.a, self._am_imm()[0]), 0)[1], 2)
        op(0xC5, lambda: (self._op_cmp(self.a, self._am_zp()[0]), 0)[1], 3)
        op(0xD5, lambda: (self._op_cmp(self.a, self._am_zpx()[0]), 0)[1], 4)
        op(0xCD, lambda: (self._op_cmp(self.a, self._am_abs()[0]), 0)[1], 4)
        op(0xDD, lambda: (lambda r: (self._op_cmp(self.a, r[0]), r[1])[1])(self._am_absx()), 4)
        op(0xD9, lambda: (lambda r: (self._op_cmp(self.a, r[0]), r[1])[1])(self._am_absy()), 4)
        op(0xC1, lambda: (self._op_cmp(self.a, self._am_indx()[0]), 0)[1], 6)
        op(0xD1, lambda: (lambda r: (self._op_cmp(self.a, r[0]), r[1])[1])(self._am_indy()), 5)
        op(0xE0, lambda: (self._op_cmp(self.x, self._am_imm()[0]), 0)[1], 2)
        op(0xE4, lambda: (self._op_cmp(self.x, self._am_zp()[0]), 0)[1], 3)
        op(0xEC, lambda: (self._op_cmp(self.x, self._am_abs()[0]), 0)[1], 4)
        op(0xC0, lambda: (self._op_cmp(self.y, self._am_imm()[0]), 0)[1], 2)
        op(0xC4, lambda: (self._op_cmp(self.y, self._am_zp()[0]), 0)[1], 3)
        op(0xCC, lambda: (self._op_cmp(self.y, self._am_abs()[0]), 0)[1], 4)

        op(0x10, lambda: self._branch(not (self.p & self.FLAG_N), self._am_rel()[0]), 2)
        op(0x30, lambda: self._branch(bool(self.p & self.FLAG_N), self._am_rel()[0]), 2)
        op(0x50, lambda: self._branch(not (self.p & self.FLAG_V), self._am_rel()[0]), 2)
        op(0x70, lambda: self._branch(bool(self.p & self.FLAG_V), self._am_rel()[0]), 2)
        op(0x90, lambda: self._branch(not (self.p & self.FLAG_C), self._am_rel()[0]), 2)
        op(0xB0, lambda: self._branch(bool(self.p & self.FLAG_C), self._am_rel()[0]), 2)
        op(0xD0, lambda: self._branch(not (self.p & self.FLAG_Z), self._am_rel()[0]), 2)
        op(0xF0, lambda: self._branch(bool(self.p & self.FLAG_Z), self._am_rel()[0]), 2)

        def _jmp_abs():
            self.pc = self._am_abs()[0]
        def _jmp_ind():
            self.pc = self._am_ind()[0]
        def _jsr():
            a = self._am_abs()[0]
            self._push16((self.pc - 1) & 0xFFFF)
            self.pc = a
        def _rts():
            self.pc = (self._pull16() + 1) & 0xFFFF
        def _rti():
            self.p = (self._pull() & ~0x10) | 0x20
            self.pc = self._pull16()
        op(0x4C, lambda: (_jmp_abs(), 0)[1], 3)
        op(0x6C, lambda: (_jmp_ind(), 0)[1], 5)
        op(0x20, lambda: (_jsr(), 0)[1], 6)
        op(0x60, lambda: (_rts(), 0)[1], 6)
        op(0x40, lambda: (_rti(), 0)[1], 6)

        def _clc(): self.p &= ~self.FLAG_C
        def _sec(): self.p |= self.FLAG_C
        def _cli(): self.p &= ~self.FLAG_I
        def _sei(): self.p |= self.FLAG_I
        def _clv(): self.p &= ~self.FLAG_V
        def _cld(): self.p &= ~self.FLAG_D
        def _sed(): self.p |= self.FLAG_D
        op(0x18, lambda: (_clc(), 0)[1], 2)
        op(0x38, lambda: (_sec(), 0)[1], 2)
        op(0x58, lambda: (_cli(), 0)[1], 2)
        op(0x78, lambda: (_sei(), 0)[1], 2)
        op(0xB8, lambda: (_clv(), 0)[1], 2)
        op(0xD8, lambda: (_cld(), 0)[1], 2)
        op(0xF8, lambda: (_sed(), 0)[1], 2)

        # NOPs (official + common unofficial)
        for c in (0xEA, 0x1A, 0x3A, 0x5A, 0x7A, 0xDA, 0xFA):
            op(c, lambda: 0, 2)
        for c in (0x80, 0x82, 0x89, 0xC2, 0xE2):
            op(c, lambda: (self._am_imm(), 0)[1], 2)
        for c in (0x04, 0x44, 0x64):
            op(c, lambda: (self._am_zp(), 0)[1], 3)
        for c in (0x14, 0x34, 0x54, 0x74, 0xD4, 0xF4):
            op(c, lambda: (self._am_zpx(), 0)[1], 4)
        op(0x0C, lambda: (self._am_abs(), 0)[1], 4)
        for c in (0x1C, 0x3C, 0x5C, 0x7C, 0xDC, 0xFC):
            op(c, lambda: (lambda r: r[1])(self._am_absx()), 4)

        def _brk():
            self.pc = (self.pc + 1) & 0xFFFF
            self._push16(self.pc)
            self._push(self.p | 0x30)
            self.p |= self.FLAG_I
            self.pc = self._read(0xFFFE) | (self._read(0xFFFF) << 8)
        op(0x00, lambda: (_brk(), 0)[1], 7)

        # ---- unofficial opcodes (complete 2A03 set) ----
        def _slo(a):
            m = self._read(a); self._write(a, m)
            self.p = (self.p & ~1) | (m >> 7)
            m = (m << 1) & 0xFF; self._write(a, m)
            self.a |= m; self._set_zn(self.a)
        def _rla(a):
            m = self._read(a); self._write(a, m); c = self.p & 1
            self.p = (self.p & ~1) | (m >> 7)
            m = ((m << 1) | c) & 0xFF; self._write(a, m)
            self.a &= m; self._set_zn(self.a)
        def _sre(a):
            m = self._read(a); self._write(a, m)
            self.p = (self.p & ~1) | (m & 1)
            m >>= 1; self._write(a, m)
            self.a ^= m; self._set_zn(self.a)
        def _rra(a):
            m = self._read(a); self._write(a, m); c = (self.p & 1) << 7
            self.p = (self.p & ~1) | (m & 1)
            m = (m >> 1) | c; self._write(a, m)
            self._adc_val(m)
        def _dcp(a):
            m = self._read(a); self._write(a, m)
            m = (m - 1) & 0xFF; self._write(a, m)
            self.p = (self.p & ~1) | (1 if self.a >= m else 0)
            self._set_zn((self.a - m) & 0xFF)
        def _isc(a):
            m = self._read(a); self._write(a, m)
            m = (m + 1) & 0xFF; self._write(a, m)
            self._adc_val(m ^ 0xFF)
        rmw_modes = (
            (lambda: self._am_zp()[0], 5), (lambda: self._am_zpx()[0], 6),
            (lambda: self._am_abs()[0], 6), (lambda: self._am_absx(True)[0], 7),
            (lambda: self._am_absy(True)[0], 7), (lambda: self._am_indx()[0], 8),
            (lambda: self._am_indy(True)[0], 8),
        )
        for fn, codes in ((_slo, (0x07, 0x17, 0x0F, 0x1F, 0x1B, 0x03, 0x13)),
                          (_rla, (0x27, 0x37, 0x2F, 0x3F, 0x3B, 0x23, 0x33)),
                          (_sre, (0x47, 0x57, 0x4F, 0x5F, 0x5B, 0x43, 0x53)),
                          (_rra, (0x67, 0x77, 0x6F, 0x7F, 0x7B, 0x63, 0x73)),
                          (_dcp, (0xC7, 0xD7, 0xCF, 0xDF, 0xDB, 0xC3, 0xD3)),
                          (_isc, (0xE7, 0xF7, 0xEF, 0xFF, 0xFB, 0xE3, 0xF3))):
            for code, (am, cy) in zip(codes, rmw_modes):
                op(code, (lambda f=fn, am=am: (f(am()), 0)[1]), cy)

        def _lax(a): self.a = self.x = self._read(a); self._set_zn(self.a)
        op(0xA7, lambda: (_lax(self._am_zp()[0]), 0)[1], 3)
        op(0xB7, lambda: (_lax(self._am_zpy()[0]), 0)[1], 4)
        op(0xAF, lambda: (_lax(self._am_abs()[0]), 0)[1], 4)
        op(0xBF, lambda: (lambda r: (_lax(r[0]), r[1])[1])(self._am_absy()), 4)
        op(0xA3, lambda: (_lax(self._am_indx()[0]), 0)[1], 6)
        op(0xB3, lambda: (lambda r: (_lax(r[0]), r[1])[1])(self._am_indy()), 5)
        op(0x87, lambda: (self._write(self._am_zp()[0], self.a & self.x), 0)[1], 3)
        op(0x97, lambda: (self._write(self._am_zpy()[0], self.a & self.x), 0)[1], 4)
        op(0x8F, lambda: (self._write(self._am_abs()[0], self.a & self.x), 0)[1], 4)
        op(0x83, lambda: (self._write(self._am_indx()[0], self.a & self.x), 0)[1], 6)

        def _imm(): return self._read(self._am_imm()[0])
        def _anc():
            self.a &= _imm(); self._set_zn(self.a)
            self.p = (self.p & ~1) | (self.a >> 7)
        def _alr():
            self.a &= _imm(); self._op_lsr_a()
        def _arr():
            self.a &= _imm()
            self.a = (self.a >> 1) | ((self.p & 1) << 7)
            self._set_zn(self.a)
            b6 = (self.a >> 6) & 1; b5 = (self.a >> 5) & 1
            self.p = (self.p & ~(self.FLAG_C | self.FLAG_V)) | b6 | ((b6 ^ b5) << 6)
        def _axs():
            r = (self.a & self.x) - _imm()
            self.p = (self.p & ~1) | (1 if r >= 0 else 0)
            self.x = r & 0xFF; self._set_zn(self.x)
        def _xaa():
            self.a = (self.a | 0xEE) & self.x & _imm(); self._set_zn(self.a)
        def _lxa():
            self.a = self.x = (self.a | 0xFF) & _imm(); self._set_zn(self.a)
        op(0x0B, lambda: (_anc(), 0)[1], 2)
        op(0x2B, lambda: (_anc(), 0)[1], 2)
        op(0x4B, lambda: (_alr(), 0)[1], 2)
        op(0x6B, lambda: (_arr(), 0)[1], 2)
        op(0xCB, lambda: (_axs(), 0)[1], 2)
        op(0x8B, lambda: (_xaa(), 0)[1], 2)
        op(0xAB, lambda: (_lxa(), 0)[1], 2)

        def _sh(value, base, index):
            addr = (base + index) & 0xFFFF
            val = value & (((base >> 8) + 1) & 0xFF)
            if (base ^ addr) & 0xFF00:
                addr = (val << 8) | (addr & 0xFF)
            self._write(addr, val)
        def _abs_base():
            b = self._read16(self.pc); self.pc = (self.pc + 2) & 0xFFFF; return b
        def _shy(): _sh(self.y, _abs_base(), self.x)
        def _shx(): _sh(self.x, _abs_base(), self.y)
        def _sha_abs(): _sh(self.a & self.x, _abs_base(), self.y)
        def _sha_ind():
            zp = self._read(self.pc); self.pc = (self.pc + 1) & 0xFFFF
            base = self._read(zp) | (self._read((zp + 1) & 0xFF) << 8)
            _sh(self.a & self.x, base, self.y)
        def _tas():
            self.sp = self.a & self.x; _sh(self.sp, _abs_base(), self.y)
        def _las():
            a, extra = self._am_absy()
            v = self._read(a) & self.sp
            self.a = self.x = self.sp = v; self._set_zn(v)
            return extra
        op(0x9C, lambda: (_shy(), 0)[1], 5)
        op(0x9E, lambda: (_shx(), 0)[1], 5)
        op(0x9F, lambda: (_sha_abs(), 0)[1], 5)
        op(0x93, lambda: (_sha_ind(), 0)[1], 6)
        op(0x9B, lambda: (_tas(), 0)[1], 5)
        op(0xBB, _las, 4)

        def _jam():
            self.pc = (self.pc - 1) & 0xFFFF
            self.jammed = True
        for c in (0x02, 0x12, 0x22, 0x32, 0x42, 0x52,
                  0x62, 0x72, 0x92, 0xB2, 0xD2, 0xF2):
            op(c, lambda: (_jam(), 0)[1], 2)

        missing = [i for i, e in enumerate(T) if e is None]
        assert not missing, "unimplemented opcodes: %r" % missing
        self._table = T

    def step(self):
        apu = self.bus.apu
        if self.pending_nmi:
            self.pending_nmi = False
            self._do_nmi()
            apu.clock(7)
            return 7
        if not (self.p & 0x04) and (self._mapper.irq_pending
                                    or apu.frame_irq_pending
                                    or apu.dmc.irq_pending):
            self._do_irq()
            apu.clock(7)
            return 7
        if self.bus.dma_stall:
            stalled = self.bus.dma_stall
            self.bus.dma_stall = 0
            self.cycles += stalled
            apu.clock(stalled)
            return stalled
        bus = self.bus
        if self.pc >= 0x8000:
            opcode = bus.mapper.cpu_read(self.pc) & 0xFF
        else:
            opcode = bus.read(self.pc) & 0xFF
        self.pc = (self.pc + 1) & 0xFFFF

        # Hot-path official opcodes.  Keeping these directly in the dispatch
        # loop avoids several lambda/addressing-mode calls for the operations
        # that dominate commercial NES games; uncommon and unofficial opcodes
        # still use the complete table below.
        code_read = bus.mapper.cpu_read if self.pc >= 0x8000 else bus.read
        cy = 0
        if opcode == 0x4C:  # JMP absolute
            lo = code_read(self.pc)
            hi = code_read((self.pc + 1) & 0xFFFF)
            self.pc = (hi << 8) | lo
            cy = 3
        elif opcode == 0xEA:  # NOP
            cy = 2
        elif opcode in (0xA9, 0xA2, 0xA0):  # LDA/LDX/LDY immediate
            value = code_read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            if opcode == 0xA9:
                self.a = value
            elif opcode == 0xA2:
                self.x = value
            else:
                self.y = value
            self._set_zn(value)
            cy = 2
        elif opcode in (0xA5, 0xB5):  # LDA zp/zp,X
            addr = code_read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            if opcode == 0xB5:
                addr = (addr + self.x) & 0xFF
            self.a = bus.read(addr)
            self._set_zn(self.a)
            cy = 4 if opcode == 0xB5 else 3
        elif opcode in (0xAD, 0xBD, 0xB9):  # LDA abs/abs,X/abs,Y
            lo = code_read(self.pc)
            hi = code_read((self.pc + 1) & 0xFFFF)
            self.pc = (self.pc + 2) & 0xFFFF
            base = (hi << 8) | lo
            index = self.x if opcode == 0xBD else (self.y if opcode == 0xB9 else 0)
            addr = (base + index) & 0xFFFF
            self.a = bus.read(addr)
            self._set_zn(self.a)
            cy = 4 + (1 if opcode != 0xAD and (base ^ addr) & 0xFF00 else 0)
        elif opcode == 0xB1:  # LDA (zp),Y
            zp = code_read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            base = bus.read(zp) | (bus.read((zp + 1) & 0xFF) << 8)
            addr = (base + self.y) & 0xFFFF
            self.a = bus.read(addr)
            self._set_zn(self.a)
            cy = 5 + (1 if (base ^ addr) & 0xFF00 else 0)
        elif opcode in (0x85, 0x95):  # STA zp/zp,X
            addr = code_read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            if opcode == 0x95:
                addr = (addr + self.x) & 0xFF
            bus.write(addr, self.a)
            cy = 4 if opcode == 0x95 else 3
        elif opcode in (0x8D, 0x9D, 0x99):  # STA abs/abs,X/abs,Y
            lo = code_read(self.pc)
            hi = code_read((self.pc + 1) & 0xFFFF)
            self.pc = (self.pc + 2) & 0xFFFF
            index = self.x if opcode == 0x9D else (self.y if opcode == 0x99 else 0)
            bus.write(((hi << 8) | lo) + index & 0xFFFF, self.a)
            cy = 5 if opcode != 0x8D else 4
        elif opcode == 0x91:  # STA (zp),Y
            zp = code_read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            addr = (bus.read(zp) | (bus.read((zp + 1) & 0xFF) << 8)) + self.y
            bus.write(addr & 0xFFFF, self.a)
            cy = 6
        elif opcode in (0xE8, 0xCA, 0xC8, 0x88):
            if opcode == 0xE8:
                self.x = (self.x + 1) & 0xFF
                value = self.x
            elif opcode == 0xCA:
                self.x = (self.x - 1) & 0xFF
                value = self.x
            elif opcode == 0xC8:
                self.y = (self.y + 1) & 0xFF
                value = self.y
            else:
                self.y = (self.y - 1) & 0xFF
                value = self.y
            self._set_zn(value)
            cy = 2
        elif opcode in (0xAA, 0x8A, 0xA8, 0x98, 0xBA, 0x9A):
            if opcode == 0xAA:
                self.x = self.a; value = self.x
            elif opcode == 0x8A:
                self.a = self.x; value = self.a
            elif opcode == 0xA8:
                self.y = self.a; value = self.y
            elif opcode == 0x98:
                self.a = self.y; value = self.a
            elif opcode == 0xBA:
                self.x = self.sp; value = self.x
            else:
                self.sp = self.x; value = None
            if value is not None:
                self._set_zn(value)
            cy = 2
        elif opcode in (0x09, 0x29, 0x49, 0x69, 0xE9, 0xC9, 0xE0, 0xC0):
            operand_addr = self.pc
            value = code_read(operand_addr)
            self.pc = (self.pc + 1) & 0xFFFF
            if opcode == 0x09:
                self.a |= value; self._set_zn(self.a)
            elif opcode == 0x29:
                self.a &= value; self._set_zn(self.a)
            elif opcode == 0x49:
                self.a ^= value; self._set_zn(self.a)
            elif opcode == 0x69:
                self._op_adc(operand_addr)
            elif opcode == 0xE9:
                self._op_sbc(operand_addr)
            elif opcode == 0xC9:
                self._op_cmp(self.a, operand_addr)
            elif opcode == 0xE0:
                self._op_cmp(self.x, operand_addr)
            else:
                self._op_cmp(self.y, operand_addr)
            cy = 2
        elif opcode in (0x10, 0x30, 0x50, 0x70, 0x90, 0xB0, 0xD0, 0xF0):
            offset = code_read(self.pc)
            self.pc = (self.pc + 1) & 0xFFFF
            condition = (
                not (self.p & self.FLAG_N) if opcode == 0x10 else
                bool(self.p & self.FLAG_N) if opcode == 0x30 else
                not (self.p & self.FLAG_V) if opcode == 0x50 else
                bool(self.p & self.FLAG_V) if opcode == 0x70 else
                not (self.p & self.FLAG_C) if opcode == 0x90 else
                bool(self.p & self.FLAG_C) if opcode == 0xB0 else
                not (self.p & self.FLAG_Z) if opcode == 0xD0 else
                bool(self.p & self.FLAG_Z)
            )
            cy = 2
            if condition:
                old_pc = self.pc
                signed = offset - 256 if offset & 0x80 else offset
                self.pc = (self.pc + signed) & 0xFFFF
                cy += 1 + (1 if (old_pc ^ self.pc) & 0xFF00 else 0)
        elif opcode in (0x18, 0x38, 0x58, 0x78, 0xB8, 0xD8, 0xF8):
            if opcode == 0x18: self.p &= ~self.FLAG_C
            elif opcode == 0x38: self.p |= self.FLAG_C
            elif opcode == 0x58: self.p &= ~self.FLAG_I
            elif opcode == 0x78: self.p |= self.FLAG_I
            elif opcode == 0xB8: self.p &= ~self.FLAG_V
            elif opcode == 0xD8: self.p &= ~self.FLAG_D
            else: self.p |= self.FLAG_D
            cy = 2
        elif opcode == 0x20:  # JSR
            lo = code_read(self.pc)
            hi = code_read((self.pc + 1) & 0xFFFF)
            self._push16((self.pc + 1) & 0xFFFF)
            self.pc = (hi << 8) | lo
            cy = 6
        elif opcode == 0x60:  # RTS
            self.pc = (self._pull16() + 1) & 0xFFFF
            cy = 6

        if cy:
            self.cycles += cy
            apu.clock(cy)
            return cy
        entry = self._table[opcode]
        if entry is None:
            self.cycles += 2
            apu.clock(2)
            return 2
        fn, base_cy = entry
        extra = fn() or 0
        cy = base_cy + extra
        self.cycles += cy
        apu.clock(cy)
        return cy


# =============================================================================
#  Engine — NES system (NTSC CPU / PPU / APU core)
# =============================================================================

class NES:
    def __init__(self, rom_path, audio=None):
        self.rom = ROM(rom_path)
        self.mapper_supported = self.rom.header.mapper in _MAPPER_TABLE
        self.mapper = make_mapper(self.rom)
        self.ppu = PPU(self.mapper)
        self.apu = APU()
        self.pad1 = Controller()
        self.pad2 = Controller()
        self.bus = Bus(self.mapper, self.ppu, self.apu, self.pad1, self.pad2)
        self.apu.bus = self.bus
        self.apu.dmc.bus = self.bus
        self.apu.audio = audio
        if self.mapper.has_audio:
            self.apu.exp_audio = self.mapper
        self.ppu.apu = self.apu
        self.cpu = CPU(self.bus)
        self.mapper.cpu = self.cpu
        self.ppu.cpu = self.cpu
        self.save_path = os.path.splitext(rom_path)[0] + ".sav"
        self._saved = b""
        self._load_battery()
        self.cpu.reset()
        self.ppu.scanline = 0
        self._cpu_target = float(self.cpu.cycles)

    # -- battery-backed PRG-RAM (.sav next to the ROM) ---------------------------
    def _load_battery(self):
        if not self.rom.header.battery or not os.path.isfile(self.save_path):
            return
        try:
            with open(self.save_path, "rb") as f:
                data = f.read()
        except OSError:
            return
        self.mapper.load_battery(data)
        self._saved = bytes(self.mapper.battery_data())

    def save_battery(self):
        if not self.rom.header.battery:
            return False
        data = bytes(self.mapper.battery_data())
        if data == self._saved:
            return False
        try:
            with open(self.save_path, "wb") as f:
                f.write(data)
        except OSError:
            return False
        self._saved = data
        return True

    def run_frame(self):
        cpu = self.cpu
        ppu = self.ppu
        step = cpu.step
        mapper = self.mapper
        mclk = mapper.cpu_clock if mapper.needs_cpu_clock else None
        line_cycles = NTSC_CYCLES_PER_SCANLINE
        hblank_at = 256.0 / 3.0
        t = self._cpu_target
        for line in range(PPU_SCANLINES):
            start = t
            end = start + line_cycles
            if line == 261 and ppu.odd_frame and (ppu.mask & 0x18):
                end -= 1.0 / 3.0
            ppu.begin_line(line, start)
            mid = start + hblank_at
            if mclk is None:
                while cpu.cycles < mid:
                    step()
                ppu.end_line(line)
                while cpu.cycles < end:
                    step()
            else:
                while cpu.cycles < mid:
                    mclk(step())
                ppu.end_line(line)
                while cpu.cycles < end:
                    mclk(step())
            t = end
        self._cpu_target = t


# =============================================================================
#  Tkinter GUI — luigines emu 0.1.1 (File/CPU/Options/Help, viewport, status)
# =============================================================================

SCALE = 2
SCREEN_W = 256
SCREEN_H = 240
APP_VERSION = "0.1.1"
WINDOW_TITLE = "luigines emu 0.1.1"

KEYMAP_P1 = {
    "x": Controller.BTN_A,
    "X": Controller.BTN_A,
    "z": Controller.BTN_B,
    "Z": Controller.BTN_B,
    "Return": Controller.BTN_START,
    "Shift_R": Controller.BTN_SELECT,
    "Shift_L": Controller.BTN_SELECT,
    "Up": Controller.BTN_UP,
    "Down": Controller.BTN_DOWN,
    "Left": Controller.BTN_LEFT,
    "Right": Controller.BTN_RIGHT,
    "w": Controller.BTN_UP, "W": Controller.BTN_UP,
    "s": Controller.BTN_DOWN, "S": Controller.BTN_DOWN,
    "a": Controller.BTN_LEFT, "A": Controller.BTN_LEFT,
    "d": Controller.BTN_RIGHT, "D": Controller.BTN_RIGHT,
}


class EmuApp:
    # Classic Windows-style chrome; game viewport stays black.
    BG = "#d4d0c8"
    VIEWPORT_BG = "#000000"
    STATUS_BG = "#d4d0c8"
    STATUS_FG = "#000000"

    def __init__(self, root, rom_path=None):
        self.root = root
        self.root.title(WINDOW_TITLE)
        self.root.configure(bg=self.BG)
        self.root.minsize(SCREEN_W * SCALE + 8, SCREEN_H * SCALE + 64)
        self.nes = None
        self.running = False
        self.paused = False
        self.audio = None
        self.fps = 0.0
        self._fps_frames = 0
        self._fps_t0 = time.perf_counter()
        self._frame_clock = time.perf_counter() + FRAME_SEC
        self._autosave_frames = 0
        self._build_menu()
        self._build_widgets()
        self._bind_keys()
        self.root.update_idletasks()
        if AUDIO_ENABLED:
            self.audio = AudioStream()
            self.audio.start()
        self.root.protocol("WM_DELETE_WINDOW", self._quit)
        if rom_path and os.path.isfile(rom_path):
            self._open(rom_path)
        else:
            self._show_splash()
        self._schedule_frame()

    def _build_menu(self):
        menubar = tk.Menu(self.root)

        m_file = tk.Menu(menubar, tearoff=0)
        m_file.add_command(label="Open ROM...", command=self._open_dialog,
                           accelerator="Ctrl+O")
        m_file.add_command(label="Close ROM", command=self._close_rom)
        m_file.add_separator()
        m_file.add_command(label="Exit", command=self._quit, accelerator="Alt+F4")
        menubar.add_cascade(label="File", menu=m_file)

        m_cpu = tk.Menu(menubar, tearoff=0)
        m_cpu.add_command(label="Reset", command=self._reset, accelerator="Ctrl+R")
        m_cpu.add_command(label="Power Cycle", command=self._power_cycle)
        m_cpu.add_separator()
        m_cpu.add_command(label="Pause", command=self._toggle_pause, accelerator="P")
        menubar.add_cascade(label="CPU", menu=m_cpu)

        m_opt = tk.Menu(menubar, tearoff=0)
        m_opt.add_command(label=f"Zoom {SCALE}x (fixed)", state="disabled")
        m_opt.add_command(label="Display... 256x240 NTSC", state="disabled")
        audio_cfg = (f"Sound... 2A03 {SAMPLE_RATE} Hz"
                     if AUDIO_ENABLED and not AUDIO_FILES else "Sound... off")
        m_opt.add_command(label=audio_cfg, state="disabled")
        m_opt.add_separator()
        m_opt.add_command(label=f"Speed... locked {TARGET_FPS:.0f} FPS",
                          state="disabled")
        m_opt.add_command(label="Input... keyboard", state="disabled")
        menubar.add_cascade(label="Options", menu=m_opt)

        m_help = tk.Menu(menubar, tearoff=0)
        m_help.add_command(label="Controls", command=self._controls_help)
        m_help.add_separator()
        m_help.add_command(label="About luigines", command=self._about)
        menubar.add_cascade(label="Help", menu=m_help)

        self.root.config(menu=menubar)

    def _build_widgets(self):
        # Status bar first so the viewport fills remaining space above it.
        status_frame = tk.Frame(self.root, bg=self.STATUS_BG, bd=1, relief="sunken")
        status_frame.pack(side="bottom", fill="x")
        self.status_var = tk.StringVar(value="No ROM loaded.")
        tk.Label(status_frame, textvariable=self.status_var, anchor="w",
                 bg=self.STATUS_BG, fg=self.STATUS_FG,
                 font=("TkDefaultFont", 9)).pack(
                     side="left", fill="x", expand=True, padx=4, pady=1)
        self.status_fps_var = tk.StringVar(value="--- fps")
        tk.Label(status_frame, textvariable=self.status_fps_var, anchor="e",
                 bg=self.STATUS_BG, fg=self.STATUS_FG,
                 font=("TkDefaultFont", 9)).pack(side="right", padx=4, pady=1)

        cw = SCREEN_W * SCALE
        ch = SCREEN_H * SCALE
        self.canvas = tk.Canvas(self.root, width=cw, height=ch,
                                bg=self.VIEWPORT_BG, highlightthickness=0, bd=0)
        self.canvas.pack(side="top", fill="both", expand=True)
        self.photo = tk.PhotoImage(width=cw, height=ch)
        self.canvas_img = self.canvas.create_image(0, 0, image=self.photo,
                                                   anchor="nw")

    def _bind_keys(self):
        self.root.bind("<KeyPress>",   self._on_key_down)
        self.root.bind("<KeyRelease>", self._on_key_up)
        self.root.bind("<Control-o>",  lambda e: self._open_dialog())
        self.root.bind("<Control-O>",  lambda e: self._open_dialog())
        self.root.bind("<Control-r>",  lambda e: self._reset())
        self.root.bind("<Control-R>",  lambda e: self._reset())
        self.root.bind("<KeyPress-p>", lambda e: self._toggle_pause())
        self.root.bind("<Pause>",      lambda e: self._toggle_pause())

    def _on_key_down(self, ev):
        bit = KEYMAP_P1.get(ev.keysym)
        if bit is not None and self.nes is not None:
            self.nes.pad1.state |= bit

    def _on_key_up(self, ev):
        bit = KEYMAP_P1.get(ev.keysym)
        if bit is not None and self.nes is not None:
            self.nes.pad1.state &= ~bit & 0xFF

    def _show_splash(self):
        cw = SCREEN_W * SCALE
        ch = SCREEN_H * SCALE
        self.photo.put("#000000", to=(0, 0, cw, ch))
        self.canvas.delete("splash")
        self.canvas.create_text(cw // 2, ch // 2 - 12, anchor="center",
                                text=WINDOW_TITLE, fill="#c0c0c0",
                                font=("TkDefaultFont", 16, "bold"), tags="splash")
        self.canvas.create_text(cw // 2, ch // 2 + 14, anchor="center",
                                text="File > Open ROM... to begin",
                                fill="#808080", font=("TkDefaultFont", 10),
                                tags="splash")

    def _hide_splash(self):
        self.canvas.delete("splash")

    def _rom_display_name(self, path):
        name = os.path.splitext(os.path.basename(path))[0]
        return name.replace("_", " ").replace(".", " ")

    def _open_dialog(self):
        path = filedialog.askopenfilename(
            title="Open NES ROM",
            filetypes=[("NES iNES ROM", "*.nes"), ("All files", "*.*")])
        if path:
            self._open(path)

    def _open(self, path):
        if self.audio is None and AUDIO_ENABLED:
            self.audio = AudioStream()
        if self.audio is not None:
            self.audio.start()
        self._save_battery()
        try:
            nes = NES(path, self.audio)
        except Exception as e:
            messagebox.showerror("luigines",
                                 f"Failed to load ROM:\n{path}\n\n{e}")
            return
        self.nes = nes
        self.running = True
        self.paused = False
        self._fps_frames = 0
        self._fps_t0 = time.perf_counter()
        self._frame_clock = time.perf_counter() + FRAME_SEC
        self._hide_splash()
        h = nes.rom.header
        note = "" if nes.mapper_supported else " (unsupported, running as NROM)"
        self.status_var.set(f"{self._rom_display_name(path)} initialized  "
                            f"[mapper {h.mapper}{note}]")
        self.status_fps_var.set("--- fps")
        self.root.title(WINDOW_TITLE)

    def _save_battery(self):
        if self.nes is not None:
            self.nes.save_battery()

    def _close_rom(self):
        self._save_battery()
        if self.nes and self.nes.apu:
            self.nes.apu.audio = None
        if self.nes and self.nes.ppu:
            self.nes.ppu.apu = None
        self.nes = None
        self.running = False
        self.status_var.set("No ROM loaded.")
        self.status_fps_var.set("--- fps")
        self.root.title(WINDOW_TITLE)
        self._show_splash()

    def _reset(self):
        if self.nes:
            self.nes.cpu.reset()
            self.nes._cpu_target = float(self.nes.cpu.cycles)
            self.nes.ppu.scanline = 0
            if self.audio and self.nes.apu:
                self.nes.apu.audio = self.audio

    def _power_cycle(self):
        if self.nes:
            path = self.nes.rom.header.filename
            self._save_battery()
            self._open(path)

    def _toggle_pause(self):
        if not self.nes:
            return
        self.paused = not self.paused
        s = self.status_var.get().replace("  [paused]", "")
        if self.paused:
            s += "  [paused]"
        self.status_var.set(s)

    def _about(self):
        messagebox.showinfo(
            "About luigines",
            f"{WINDOW_TITLE}\n"
            f"Single-file NES emulator, Python {sys.version.split()[0]}\n\n"
            "Menus: File, CPU, Options, Help.\n"
            f"Display locked at {TARGET_FPS:.0f} FPS NTSC.\n"
            "PPU: 256x240. APU: cycle-driven 2A03 synthesis.\n"
            "CPU: all 256 2A03 opcodes (official + unofficial).\n"
            "Mappers: " + ", ".join(str(m) for m in sorted(_MAPPER_TABLE)) + "."
            "\nBattery saves: <rom>.sav next to the ROM.")

    def _controls_help(self):
        messagebox.showinfo(
            "Controls",
            "D-Pad  : Arrow keys (or WASD)\n"
            "A      : X\n"
            "B      : Z\n"
            "Start  : Enter\n"
            "Select : Shift\n\n"
            "Pause  : P  (or Pause key)\n"
            "Reset  : Ctrl+R\n"
            "Open   : Ctrl+O")

    def _quit(self):
        self._save_battery()
        self.running = False
        if self.audio:
            self.audio.stop()
        try:
            self.root.destroy()
        except tk.TclError:
            pass

    def _schedule_frame(self):
        self.root.after(1, self._frame_tick)

    def _update_fps(self, frames=1):
        self._fps_frames += frames
        dt = time.perf_counter() - self._fps_t0
        if dt >= 1.0:
            self.fps = self._fps_frames / dt
            self._fps_frames = 0
            self._fps_t0 = time.perf_counter()
            self.status_fps_var.set(f"{self.fps:.0f} fps")

    def _frame_tick(self):
        now = time.perf_counter()
        if not (self.nes and self.running and not self.paused):
            self._frame_clock = now + FRAME_SEC
            self.root.after(max(1, math.ceil(FRAME_SEC * 1000)), self._frame_tick)
            return
        if now < self._frame_clock:
            delay = self._frame_clock - now
            self.root.after(max(1, math.ceil(delay * 1000)), self._frame_tick)
            return

        frames = 0
        try:
            # Catch up one hidden frame after a small OS/UI scheduling hiccup,
            # then blit once.  This keeps CPU/APU time at 60 Hz without letting
            # a delayed Tk callback create an ever-growing audio backlog.
            while frames < 2 and now >= self._frame_clock:
                self.nes.run_frame()
                frames += 1
                self._frame_clock += FRAME_SEC
                now = time.perf_counter()
            self._blit()
            self._update_fps(frames)
            self._autosave_frames += frames
            if self._autosave_frames >= 600:
                self._autosave_frames = 0
                self._save_battery()
        except Exception as e:
            self.running = False
            self.status_var.set(f"emulation error: {e}")
        now = time.perf_counter()
        if now - self._frame_clock > FRAME_SEC * 2:
            self._frame_clock = now + FRAME_SEC
        delay = max(0.0, self._frame_clock - now)
        self.root.after(max(1, math.ceil(delay * 1000)), self._frame_tick)

    def _blit(self):
        if self.nes is None:
            return
        fb = self.nes.ppu.framebuffer
        try:
            rgb = b"".join(NES_PALETTE_BYTES[pixel & 0x3F] for pixel in fb)
            ppm = b"P6\n256 240\n255\n" + rgb
            tmp = tk.PhotoImage(data=ppm, format="PPM")
            self.photo = tmp.zoom(SCALE, SCALE)
            self.canvas.itemconfig(self.canvas_img, image=self.photo)
        except tk.TclError:
            # Conservative fallback for Tk builds without binary PPM support.
            pal = NES_PALETTE_HEX
            rows = []
            for y in range(SCREEN_H):
                off = y * SCREEN_W
                rows.append("{" + " ".join(
                    pal[fb[off + x] & 0x3F] for x in range(SCREEN_W)) + "}")
            tmp = tk.PhotoImage(width=SCREEN_W, height=SCREEN_H)
            tmp.put(" ".join(rows))
            self.photo = tmp.zoom(SCALE, SCALE)
            self.canvas.itemconfig(self.canvas_img, image=self.photo)


def main():
    if sys.version_info < (3, 14):
        print(f"{WINDOW_TITLE} requires Python 3.14+, got {sys.version}",
              file=sys.stderr)
        return 1
    rom = sys.argv[1] if len(sys.argv) > 1 else None
    root = tk.Tk()
    EmuApp(root, rom)
    root.mainloop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
