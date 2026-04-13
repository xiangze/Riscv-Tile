#!/usr/bin/env python3
"""
tests/scripts/elf2hex.py
ELF バイナリ → Verilog $readmemh 形式 hex 変換ツール

使い方:
  python3 elf2hex.py <input.elf> <output.hex> [--words N]

出力フォーマット:
  各行が 32bit ワード (little-endian) のリトルエンディアン hex 値
  Chisel の loadMemoryFromFile / Verilog $readmemh で直接ロード可能

例:
  00000000: @00000000
  00000004: deadbeef
  ...

オプション:
  --words N   出力ワード数 (デフォルト 16384 = 64KB / 4)
              TileConfig.iMemSize と合わせること
"""

import sys
import struct
import argparse
from pathlib import Path

# ── ELF パーサ（外部ライブラリ不要の最小実装） ────────────────────────────────

ELF_MAGIC      = b'\x7fELF'
PT_LOAD        = 1

def parse_elf(data: bytes) -> list[tuple[int, bytes]]:
    """ELF から LOAD セグメントを抽出して (vaddr, data) のリストを返す"""
    if data[:4] != ELF_MAGIC:
        raise ValueError("Not a valid ELF file")

    ei_class = data[4]   # 1=32bit, 2=64bit
    ei_data  = data[5]   # 1=LE,    2=BE
    endian   = '<' if ei_data == 1 else '>'

    if ei_class == 1:    # ELF32
        # ELF header
        e_phoff, = struct.unpack_from(f'{endian}I', data, 0x1c)
        e_phentsize, = struct.unpack_from(f'{endian}H', data, 0x2a)
        e_phnum,     = struct.unpack_from(f'{endian}H', data, 0x2c)

        segments = []
        for i in range(e_phnum):
            off = e_phoff + i * e_phentsize
            p_type,   = struct.unpack_from(f'{endian}I', data, off + 0x00)
            p_offset, = struct.unpack_from(f'{endian}I', data, off + 0x04)
            p_vaddr,  = struct.unpack_from(f'{endian}I', data, off + 0x08)
            p_filesz, = struct.unpack_from(f'{endian}I', data, off + 0x10)
            p_memsz,  = struct.unpack_from(f'{endian}I', data, off + 0x14)
            if p_type == PT_LOAD and p_filesz > 0:
                seg_data = data[p_offset:p_offset + p_filesz]
                # memsz > filesz の部分は BSS (ゼロパディング)
                seg_data += b'\x00' * (p_memsz - p_filesz)
                segments.append((p_vaddr, seg_data))
    else:                # ELF64
        e_phoff, = struct.unpack_from(f'{endian}Q', data, 0x20)
        e_phentsize, = struct.unpack_from(f'{endian}H', data, 0x36)
        e_phnum,     = struct.unpack_from(f'{endian}H', data, 0x38)

        segments = []
        for i in range(e_phnum):
            off = e_phoff + i * e_phentsize
            p_type,   = struct.unpack_from(f'{endian}I', data, off + 0x00)
            p_offset, = struct.unpack_from(f'{endian}Q', data, off + 0x08)
            p_vaddr,  = struct.unpack_from(f'{endian}Q', data, off + 0x10)
            p_filesz, = struct.unpack_from(f'{endian}Q', data, off + 0x20)
            p_memsz,  = struct.unpack_from(f'{endian}Q', data, off + 0x28)
            if p_type == PT_LOAD and p_filesz > 0:
                seg_data = data[p_offset:p_offset + p_filesz]
                seg_data += b'\x00' * (p_memsz - p_filesz)
                segments.append((p_vaddr, seg_data))

    return segments


def elf_to_words(elf_path: Path, num_words: int) -> list[int]:
    """ELF を読み込み、アドレス 0 から始まる word 配列を返す"""
    data = elf_path.read_bytes()
    segments = parse_elf(data)

    mem = [0] * num_words

    for vaddr, seg_data in segments:
        # ワードアドレスへ変換（バイトアドレスを 4 で割る）
        word_base = vaddr >> 2
        # セグメントデータをワード単位で書き込む
        for i in range(0, len(seg_data), 4):
            chunk = seg_data[i:i+4]
            if len(chunk) < 4:
                chunk = chunk + b'\x00' * (4 - len(chunk))
            word_idx = word_base + i // 4
            if 0 <= word_idx < num_words:
                mem[word_idx] = struct.unpack_from('<I', chunk)[0]  # little-endian

    return mem


def write_memh(mem: list[int], out_path: Path) -> None:
    """Verilog $readmemh フォーマットで書き出す
    
    非ゼロ領域だけを @address ディレクティブで区切って出力することで
    ファイルサイズを削減する。
    """
    lines = []
    last_nonzero = max((i for i, v in enumerate(mem) if v != 0), default=-1)

    if last_nonzero < 0:
        # 全ゼロ（テストが空）
        lines.append("// empty")
    else:
        i = 0
        while i <= last_nonzero:
            # 連続するゼロ列はアドレスジャンプでスキップ
            if mem[i] == 0:
                j = i + 1
                while j <= last_nonzero and mem[j] == 0:
                    j += 1
                if j > last_nonzero:
                    break
                lines.append(f"@{j:08x}")
                i = j
            else:
                lines.append(f"{mem[i]:08x}")
                i += 1

    out_path.write_text('\n'.join(lines) + '\n')


# ── メインエントリ ────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description='ELF → Verilog $readmemh hex converter for TileRiscV')
    parser.add_argument('elf',  type=Path, help='Input ELF file')
    parser.add_argument('hex',  type=Path, help='Output .hex file')
    parser.add_argument('--words', type=int, default=16384,
                        help='Memory size in 32-bit words (default: 16384 = 64KB)')
    args = parser.parse_args()

    if not args.elf.exists():
        print(f'ERROR: {args.elf} not found', file=sys.stderr)
        sys.exit(1)

    mem = elf_to_words(args.elf, args.words)
    write_memh(mem, args.hex)

    used = sum(1 for v in mem if v != 0)
    print(f'  {args.elf.name} → {args.hex.name}  '
          f'({used} non-zero words / {args.words} total)')


if __name__ == '__main__':
    main()
