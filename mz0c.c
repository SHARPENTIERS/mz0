/* Source modified to compress a MZF file into a MZ0 file */
/*
 * (c) Copyright 2021 by Einar Saukas. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * The name of its author may not be used to endorse or promote products
 *       derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>

/*- zx7.h ---------------------------------------------------*/

#define INITIAL_OFFSET 1

#define FALSE 0
#define TRUE 1

typedef struct block_t {
    struct block_t *chain;
    struct block_t *ghost_chain;
    int bits;
    int index;
    int offset;
    int length;
    int references;
} BLOCK;

BLOCK *allocate(int bits, int index, int offset, int length, BLOCK *chain);

void assign(BLOCK **ptr, BLOCK *chain);

BLOCK *optimize(unsigned char *input_data, int input_size, int skip, int offset_limit);

unsigned char *compress(BLOCK *optimal, unsigned char *input_data, int input_size, int skip, int backwards_mode, int *output_size, int *delta);

/*- memory.c ------------------------------------------------*/

#define QTY_BLOCKS 10000

BLOCK *ghost_root = NULL;
BLOCK *dead_array = NULL;
int dead_array_size = 0;

BLOCK *allocate(int bits, int index, int offset, int length, BLOCK *chain) {
    BLOCK *ptr;

    if (ghost_root) {
        ptr = ghost_root;
        ghost_root = ptr->ghost_chain;
        if (ptr->chain) {
            if (!--ptr->chain->references) {
                ptr->chain->ghost_chain = ghost_root;
                ghost_root = ptr->chain;
            }
        }
    } else {
        if (!dead_array_size) {
            dead_array = (BLOCK *)malloc(QTY_BLOCKS*sizeof(BLOCK));
            if (!dead_array) {
                fprintf(stderr, "Error: Insufficient memory\n");
                exit(1);
            }
            dead_array_size = QTY_BLOCKS;
        }
        ptr = &dead_array[--dead_array_size];
    }
    ptr->bits = bits;
    ptr->index = index;
    ptr->offset = offset;
    ptr->length = length;
    if (chain)
        chain->references++;
    ptr->chain = chain;
    ptr->references = 0;
    return ptr;
}

void assign(BLOCK **ptr, BLOCK *chain) {
    chain->references++;
    if (*ptr) {
        if (!--(*ptr)->references) {
            (*ptr)->ghost_chain = ghost_root;
            ghost_root = *ptr;
        }
    }
    *ptr = chain;
}

/*- optimze.c -----------------------------------------------*/

#define minimum(a,b) (a < b ? a : b)

int offset_ceiling(int index, int offset_limit) {
    return index > offset_limit ? offset_limit : index < INITIAL_OFFSET ? INITIAL_OFFSET : index;
}

int elias_gamma_bits(int value) {
    int bits = 1;
    while (value > 1) {
        bits += 2;
        value >>= 1;
    }
    return bits;
}

BLOCK* optimize(unsigned char *input_data, int input_size, int skip, int offset_limit) {
    BLOCK **last_literal;
    BLOCK **last_match;
    BLOCK **optimal;
    int* match_length;
    int* best_length;
    int best_length_size;
    int bits;
    int index;
    int offset;
    int length;
    int bits2;
    int max_offset = offset_ceiling(input_size-1, offset_limit);

    /* allocate all main data structures at once */
    last_literal = (BLOCK **)calloc(max_offset+1, sizeof(BLOCK *));
    last_match = (BLOCK **)calloc(max_offset+1, sizeof(BLOCK *));
    optimal = (BLOCK **)calloc(input_size+1, sizeof(BLOCK *));
    match_length = (int *)calloc(max_offset+1, sizeof(int));
    best_length = (int *)malloc((input_size+1)*sizeof(int));
    if (!last_literal || !last_match || !optimal || !match_length || !best_length) {
         fprintf(stderr, "Error: Insufficient memory\n");
         exit(1);
    }
    best_length[2] = 2;

    /* start with fake block */
    assign(&(last_match[INITIAL_OFFSET]), allocate(-1, skip-1, INITIAL_OFFSET, 0, NULL));

    /* process remaining bytes */
    for (index = skip; index < input_size; index++) {
        best_length_size = 2;
        max_offset = offset_ceiling(index, offset_limit);
        for (offset = 1; offset <= max_offset; offset++) {
            if (index >= offset && input_data[index] == input_data[index-offset]) {
                /* copy from last offset */
                if (last_literal[offset]) {
                    length = index-last_literal[offset]->index;
                    bits = last_literal[offset]->bits + 1 + elias_gamma_bits(length);
                    assign(&(last_match[offset]), allocate(bits, index, offset, length, last_literal[offset]));
                    if (!optimal[index] || optimal[index]->bits > bits)
                        assign(&(optimal[index]), last_match[offset]);
                }
                /* copy from new offset */
                if (++match_length[offset] > 1) {
                    if (best_length_size < match_length[offset]) {
                        bits = optimal[index-best_length[best_length_size]]->bits + elias_gamma_bits(best_length[best_length_size]-1);
                        do {
                            best_length_size++;
                            bits2 = optimal[index-best_length_size]->bits + elias_gamma_bits(best_length_size-1);
                            if (bits2 <= bits) {
                                best_length[best_length_size] = best_length_size;
                                bits = bits2;
                            } else {
                                best_length[best_length_size] = best_length[best_length_size-1];
                            }
                        } while(best_length_size < match_length[offset]);
                    }
                    length = best_length[match_length[offset]];
                    bits = optimal[index-length]->bits + 8 + elias_gamma_bits((offset-1)/128+1) + elias_gamma_bits(length-1);
                    if (!last_match[offset] || last_match[offset]->index != index || last_match[offset]->bits > bits) {
                        assign(&last_match[offset], allocate(bits, index, offset, length, optimal[index-length]));
                        if (!optimal[index] || optimal[index]->bits > bits)
                            assign(&(optimal[index]), last_match[offset]);
                    }
                }
            } else {
                /* copy literals */
                match_length[offset] = 0;
                if (last_match[offset]) {
                    length = index-last_match[offset]->index;
                    bits = last_match[offset]->bits + 1 + elias_gamma_bits(length) + length*8;
                    assign(&(last_literal[offset]), allocate(bits, index, 0, length, last_match[offset]));
                    if (!optimal[index] || optimal[index]->bits > bits)
                        assign(&(optimal[index]), last_literal[offset]);
                }
            }
        }
    }

    return optimal[input_size-1];
}

/*- compress.c ----------------------------------------------*/

unsigned char* output_data;
int output_index;
int input_index;
int bit_index;
int bit_mask;
int diff;
int backtrack;

void read_bytes(int n, int *delta) {
    input_index += n;
    diff += n;
    if (diff > *delta)
        *delta = diff;
}

void write_byte(int value) {
    output_data[output_index++] = value;
    diff--;
}

void write_bit(int value) {
    if (backtrack) {
        if (value)
            output_data[output_index-1] |= 1;
        backtrack = FALSE;
    } else {
        if (!bit_mask) {
            bit_mask = 128;
            bit_index = output_index;
            write_byte(0);
        }
        if (value)
            output_data[bit_index] |= bit_mask;
        bit_mask >>= 1;
    }
}

void write_interlaced_elias_gamma(int value, int backwards_mode) {
    int i;

    for (i = 2; i <= value; i <<= 1)
        ;
    i >>= 1;
    while ((i >>= 1) > 0) {
        write_bit(backwards_mode);
        write_bit(value & i);
    }
    write_bit(!backwards_mode);
}

unsigned char *compress(BLOCK *optimal, unsigned char *input_data, int input_size, int skip, int backwards_mode, int *output_size, int *delta) {
    BLOCK *next;
    BLOCK *prev;
    int last_offset = INITIAL_OFFSET;
    int first = TRUE;
    int i;

    /* calculate and allocate output buffer */
    *output_size = (optimal->bits+18+7)/8;
    output_data = (unsigned char *)malloc(*output_size);
    if (!output_data) {
         fprintf(stderr, "Error: Insufficient memory\n");
         exit(1);
    }

    /* initialize delta */
    diff = *output_size-input_size+skip;
    *delta = 0;

    /* un-reverse optimal sequence */
    next = NULL;
    while (optimal) {
        prev = optimal->chain;
        optimal->chain = next;
        next = optimal;
        optimal = prev;
    }

    input_index = skip;
    output_index = 0;
    bit_mask = 0;

    for (optimal = next->chain; optimal; optimal = optimal->chain) {
        if (!optimal->offset) {
            /* copy literals indicator */
            if (first)
                first = FALSE;
            else
                write_bit(0);

            /* copy literals length */
            write_interlaced_elias_gamma(optimal->length, backwards_mode);

            /* copy literals values */
            for (i = 0; i < optimal->length; i++) {
                write_byte(input_data[input_index]);
                read_bytes(1, delta);
            }
        } else if (optimal->offset == last_offset) {
            /* copy from last offset indicator */
            write_bit(0);

            /* copy from last offset length */
            write_interlaced_elias_gamma(optimal->length, backwards_mode);
            read_bytes(optimal->length, delta);
        } else {
            /* copy from new offset indicator */
            write_bit(1);

            /* copy from new offset MSB */
            write_interlaced_elias_gamma((optimal->offset-1)/128+1, backwards_mode);

            /* copy from new offset LSB */
            if (backwards_mode)
                write_byte(((optimal->offset-1)%128)<<1);
            else
                write_byte((255-((optimal->offset-1)%128))<<1);
            backtrack = TRUE;

            /* copy from new offset length */
            write_interlaced_elias_gamma(optimal->length-1, backwards_mode);
            read_bytes(optimal->length, delta);

            last_offset = optimal->offset;
        }
    }

    /* end marker */
    write_bit(1);
    write_interlaced_elias_gamma(256, backwards_mode);

    return output_data;
}

/*- MZF specifics -------------------------------------------*/

typedef struct header_t {
    unsigned char file_attribute;
    char file_name[17];
    unsigned short file_size;
    unsigned short file_load;
    unsigned short file_exec;
    char comment[104];
} Header;

void fill_header_and_loader(Header *header, char *loader, size_t *size, size_t skip, size_t output_size, int backwards_mode, long delta) {
    unsigned short original_size = header->file_size;
    unsigned short original_load = header->file_load;
    unsigned short original_exec = header->file_exec;
    char *memory;
    size_t loader_addr;
    size_t loader_size = 0;

    printf(
        "[Old file] size: %5d (%04x), load: %04x, exec: %04x\n",
        original_size, original_size,
        original_load,
        original_exec);

    if (backwards_mode) {
        memcpy(
            loader + 0x20,
            /*
11A3                    .ORG $11A3
11A3                    ; -----------------------------------------------------------------------------
11A3                    ; ZX0 decoder by Einar Saukas
11A3                    ; "Standard" version (69 bytes only) - BACKWARDS VARIANT
11A3                    ; -----------------------------------------------------------------------------
11A3                    ; Parameters:
11A3                    ;   HL: last source address (compressed data)
11A3                    ;   DE: last destination address (decompressing)
11A3                    ; -----------------------------------------------------------------------------
11A3 */"\x0D"        /*        db       $0D
11A4                    _main:
11A4 */"\x21\x00\x00"/*        ld       hl,$0000            ; last source address
11A7 */"\x11\x00\x00"/*        ld       de,$0000            ; last target address
11AA */"\x01\xAD\x00"/*        ld       bc,$00AD            ; executable address
11AD */"\xC5"        /*        push     bc
11AE                    dzx0_standard_back:
11AE */"\x01\x01\x00"/*        ld       bc,1                ; preserve default offset 1
11B1 */"\xC5"        /*        push     bc
11B2 */"\x0D"        /*        dec      c
11B3 */"\x3E\x80"    /*        ld       a,$80
11B5                    dzx0sb_literals:
11B5 */"\xCD\xE4\x11"/*        call     dzx0sb_elias        ; obtain length
11B8 */"\xED\xB8"    /*        lddr                         ; copy literals
11BA */"\x87"        /*        add      a,a                 ; copy from last offset or new offset?
11BB */"\x38\x0D"    /*        jr       c,dzx0sb_new_offset
11BD */"\xCD\xE4\x11"/*        call     dzx0sb_elias        ; obtain length
11C0                    dzx0sb_copy:
11C0 */"\xE3"        /*        ex       (sp),hl             ; preserve source, restore offset
11C1 */"\xE5"        /*        push     hl                  ; preserve offset
11C2 */"\x19"        /*        add      hl,de               ; calculate destination - offset
11C3 */"\xED\xB8"    /*        lddr                         ; copy from offset
11C5 */"\xE1"        /*        pop      hl                  ; restore offset
11C6 */"\xE3"        /*        ex       (sp),hl             ; preserve offset, restore source
11C7 */"\x87"        /*        add      a,a                 ; copy from literals or new offset?
11C8 */"\x30\xEB"    /*        jr       nc,dzx0sb_literals
11CA                    dzx0sb_new_offset:
11CA */"\x33"        /*        inc      sp                  ; discard last offset
11CB */"\x33"        /*        inc      sp
11CC */"\xCD\xE4\x11"/*        call     dzx0sb_elias        ; obtain offset MSB
11CF */"\x05"        /*        dec      b
11D0 */"\xC8"        /*        ret      z                   ; check end marker
11D1 */"\x0D"        /*        dec      c                   ; adjust for positive offset
11D2 */"\x41"        /*        ld       b,c
11D3 */"\x4E"        /*        ld       c,(hl)              ; obtain offset LSB
11D4 */"\x2B"        /*        dec      hl
11D5 */"\xCB\x38"    /*        srl      b                   ; last offset bit becomes first length bit
11D7 */"\xCB\x19"    /*        rr       c
11D9 */"\x03"        /*        inc      bc
11DA */"\xC5"        /*        push     bc                  ; preserve new offset
11DB */"\x01\x01\x00"/*        ld       bc,1                ; obtain length
11DE */"\xDC\xEC\x11"/*        call     c,dzx0sb_elias_backtrack
11E1 */"\x03"        /*        inc      bc
11E2 */"\x18\xDC"    /*        jr       dzx0sb_copy
11E4                    dzx0sb_elias:
11E4 */"\x0C"        /*        inc      c                   ; inverted interlaced Elias gamma coding
11E5                    dzx0sb_elias_loop:
11E5 */"\x87"        /*        add      a,a
11E6 */"\x20\x03"    /*        jr       nz,dzx0sb_elias_skip
11E8 */"\x7E"        /*        ld       a,(hl)              ; load another group of 8 bits
11E9 */"\x2B"        /*        dec      hl
11EA */"\x17"        /*        rla
11EB                    dzx0sb_elias_skip:
11EB */"\xD0"        /*        ret      nc
11EC                    dzx0sb_elias_backtrack:
11EC */"\x87"        /*        add      a,a
11ED */"\xCB\x11"    /*        rl       c
11EF */"\xCB\x10"    /*        rl       b
11F1 */"\x18\xF2"    /*        jr       dzx0sb_elias_loop
11F3                    ; -----------------------------------------------------------------------------
            */,
            (loader_size = 0x11F3-0x11A3)
        );

        /*
               header   compressed data   loader
             |--------|-----------------|--------|
                   header           decompressed data            suffix
                 |--------|---------------------------------|--------------|
                                                       << start
                      <--->                                 <-------------->
                      delta                                       skip
        */

        original_size -= skip;

        loader_size += 0x20;

        header->file_size = output_size + loader_size;
        header->file_load = original_load - delta;
        header->file_exec = header->file_load + output_size;

        loader_addr = header->file_exec;

        memory = loader + 0x20 - 0x11A3;

        *((unsigned short*)(memory+0x11A5)) = original_load - delta + output_size-1;
        *((unsigned short*)(memory+0x11A8)) = original_load + original_size-1;
        *((unsigned short*)(memory+0x11AB)) = original_exec;

        loader[0x00] = 0x21;                              // 21 xx xx         ld      hl,$xxxx
        loader[0x01] = (original_size >> 0) & 255;
        loader[0x02] = (original_size >> 8) & 255;
        loader[0x03] = 0x22;                              // 22 xx xx         ld      ($1102),hl
        loader[0x04] = 0x02;
        loader[0x05] = 0x11;

        loader[0x06] = 0x21;                              // 21 xx xx         ld      hl,$xxxx
        loader[0x07] = (original_load >> 0) & 255;
        loader[0x08] = (original_load >> 8) & 255;
        loader[0x09] = 0x22;                              // 22 xx xx         ld      ($1104),hl
        loader[0x0A] = 0x04;
        loader[0x0B] = 0x11;

        loader[0x0C] = 0x21;                              // 21 xx xx         ld      hl,$xxxx
        loader[0x0D] = (original_exec >> 0) & 255;
        loader[0x0E] = (original_exec >> 8) & 255;
        loader[0x0F] = 0x22;                              // 22 xx xx         ld      ($1106),hl
        loader[0x10] = 0x06;
        loader[0x11] = 0x11;

        loader[0x12] = 0x21;                              // 21 xx xx         ld      hl,$xxxx
        loader[0x13] = ((loader_addr + 0x20) >> 0) & 255;
        loader[0x14] = ((loader_addr + 0x20) >> 8) & 255;

        loader[0x15] = 0x11;                              // 11 A3 11         ld      de,$11A3
        loader[0x16] = 0xA3;
        loader[0x17] = 0x11;

        loader[0x18] = 0x01;                              // 01 xx xx         ld      bc,$xxxx
        loader[0x19] = ((loader_size - 0x20) >> 0) & 255;
        loader[0x1A] = ((loader_size - 0x20) >> 8) & 255;

        loader[0x1B] = 0xED;                              // ED B0            ldir
        loader[0x1C] = 0xB0;

        loader[0x1D] = 0xC3;                              // C3 A4 11         jp      $11A4
        loader[0x1E] = 0xA4;
        loader[0x1F] = 0x11;
    } else {
        memcpy(
            loader + 0x20,
            /*
11A3                    .ORG $11A3
11A3                    ; -----------------------------------------------------------------------------
11A3                    ; ZX0 decoder by Einar Saukas
11A3                    ; "Standard" version (69 bytes only)
11A3                    ; -----------------------------------------------------------------------------
11A3                    ; Parameters:
11A3                    ;   HL: last source address (compressed data)
11A3                    ;   DE: last destination address (decompressing)
11A3                    ; -----------------------------------------------------------------------------
11A3 */"\x0D"        /*        db      $0D
11A4                    _main:
11A4 */"\x21\x00\x00"/*        ld      hl,$0000             ; first source address
11A7 */"\x11\x00\x00"/*        ld      de,$0000             ; first target address
11AA */"\x01\xAD\x00"/*        ld      bc,$00AD             ; executable address
11AD */"\xC5"        /*        push    bc
11AE                    dzx0_standard:
11AE */"\x01\xFF\xFF"/*        ld       bc,$FFFF            ; preserve default offset -1
11B1 */"\xC5"        /*        push     bc
11B2 */"\x03"        /*        inc      bc
11B3 */"\x3E\x80"    /*        ld       a,$80
11B5                    dzx0s_literals:
11B5 */"\xCD\xE4\x11"/*        call     dzx0s_elias         ; obtain length
11B8 */"\xED\xB0"    /*        ldir                         ; copy literals
11BA */"\x87"        /*        add      a,a                 ; copy from last offset or new offset?
11BB */"\x38\x0D"    /*        jr       c,dzx0s_new_offset
11BD */"\xCD\xE4\x11"/*        call     dzx0s_elias         ; obtain length
11C0                    dzx0s_copy:
11C0 */"\xE3"        /*        ex       (sp),hl             ; preserve source, restore offset
11C1 */"\xE5"        /*        push     hl                  ; preserve offset
11C2 */"\x19"        /*        add      hl,de               ; calculate destination - offset
11C3 */"\xED\xB0"    /*        ldir                         ; copy from offset
11C5 */"\xE1"        /*        pop      hl                  ; restore offset
11C6 */"\xE3"        /*        ex       (sp),hl             ; preserve offset, restore source
11C7 */"\x87"        /*        add      a,a                 ; copy from literals or new offset?
11C8 */"\x30\xEB"    /*        jr       nc,dzx0s_literals
11CA                    dzx0s_new_offset:
11CA */"\xCD\xE4\x11"/*        call     dzx0s_elias         ; obtain offset MSB
11CD */"\x08"        /*        ex       af,af'
11CE */"\xF1"        /*        pop      af                  ; discard last offset
11CF */"\xAF"        /*        xor      a                   ; adjust for negative offset
11D0 */"\x91"        /*        sub      c
11D1 */"\xC8"        /*        ret      z                   ; check end marker
11D2 */"\x47"        /*        ld       b,a
11D3 */"\x08"        /*        ex       af,af'
11D4 */"\x4E"        /*        ld       c,(hl)              ; obtain offset LSB
11D5 */"\x23"        /*        inc      hl
11D6 */"\xCB\x18"    /*        rr       b                   ; last offset bit becomes first length bit
11D8 */"\xCB\x19"    /*        rr       c
11DA */"\xC5"        /*        push     bc                  ; preserve new offset
11DB */"\x01\x01\x00"/*        ld       bc,1                ; obtain length
11DE */"\xD4\xEC\x11"/*        call     nc,dzx0s_elias_backtrack
11E1 */"\x03"        /*        inc      bc
11E2 */"\x18\xDC"    /*        jr       dzx0s_copy
11E4                    dzx0s_elias:
11E4 */"\x0C"        /*        inc      c                   ; interlaced Elias gamma coding
11E5                    dzx0s_elias_loop:
11E5 */"\x87"        /*        add      a,a
11E6 */"\x20\x03"    /*        jr       nz,dzx0s_elias_skip
11E8 */"\x7E"        /*        ld       a,(hl)              ; load another group of 8 bits
11E9 */"\x23"        /*        inc      hl
11EA */"\x17"        /*        rla
11EB                    dzx0s_elias_skip:
11EB */"\xD8"        /*        ret      c
11EC                    dzx0s_elias_backtrack:
11EC */"\x87"        /*        add      a,a
11ED */"\xCB\x11"    /*        rl       c
11EF */"\xCB\x10"    /*        rl       b
11F1 */"\x18\xF2"    /*        jr       dzx0s_elias_loop
11F3                    ; -----------------------------------------------------------------------------
            */,
            (loader_size = 0x11F3-0x11A3)
        );

        /*
                                           header   loader   compressed data
                                         |--------|--------|-----------------|
                 header      prefix             decompressed data
               |--------|--------------|---------------------------------|
                                     start >>
                        <-------------->                                 <--->
                              skip                                       delta
        */

        original_size -= skip;
        original_load += skip;

        loader_size += 0x20;

        if (delta < loader_size) {
            delta = loader_size;
        }

        header->file_size = loader_size + output_size;
        header->file_load = original_load + original_size + delta - header->file_size;
        header->file_exec = header->file_load;

        loader_addr = header->file_exec;

        memory = loader + 0x20 - 0x11A3;

        *((unsigned short*)(memory+0x11A5)) = original_load + original_size + delta - output_size;
        *((unsigned short*)(memory+0x11A8)) = original_load;
        *((unsigned short*)(memory+0x11AB)) = original_exec;

        loader[0x00] = 0x21;                              // 01 xx xx         ld      hl,$xxxx
        loader[0x01] = (original_size >> 0) & 255;
        loader[0x02] = (original_size >> 8) & 255;
        loader[0x03] = 0x22;                              // 22 xx xx         ld      ($1102),hl
        loader[0x04] = 0x02;
        loader[0x05] = 0x11;

        loader[0x06] = 0x21;                              // 01 xx xx         ld      hl,$xxxx
        loader[0x07] = (original_load >> 0) & 255;
        loader[0x08] = (original_load >> 8) & 255;
        loader[0x09] = 0x22;                              // 22 xx xx         ld      ($1104),hl
        loader[0x0A] = 0x04;
        loader[0x0B] = 0x11;

        loader[0x0C] = 0x21;                              // 01 xx xx         ld      hl,$xxxx
        loader[0x0D] = (original_exec >> 0) & 255;
        loader[0x0E] = (original_exec >> 8) & 255;
        loader[0x0F] = 0x22;                              // 22 xx xx         ld      ($1106),hl
        loader[0x10] = 0x06;
        loader[0x11] = 0x11;

        loader[0x12] = 0x21;                              // 21 xx xx         ld      hl,$xxxx
        loader[0x13] = ((loader_addr + 0x20) >> 0) & 255;
        loader[0x14] = ((loader_addr + 0x20) >> 8) & 255;

        loader[0x15] = 0x11;                              // 11 A3 11         ld      de,$11A3
        loader[0x16] = 0xA3;
        loader[0x17] = 0x11;

        loader[0x18] = 0x01;                              // 01 xx xx         ld      bc,$xxxx
        loader[0x19] = ((loader_size - 0x20) >> 0) & 255;
        loader[0x1A] = ((loader_size - 0x20) >> 8) & 255;

        loader[0x1B] = 0xED;                              // ED B0            ldir
        loader[0x1C] = 0xB0;

        loader[0x1D] = 0xC3;                              // C3 A4 11         jp      $11A4
        loader[0x1E] = 0xA4;
        loader[0x1F] = 0x11;
    }

    *size = loader_size;

    printf(
        "[New file] size: %5d (%04x), load: %04x, exec: %04x\n",
        header->file_size, header->file_size,
        header->file_load, header->file_exec);
}

/*- zx0.c (modified to compress MZF into MZ0 ----------------*/

#define MAX_OFFSET_ZX0    32640
#define MAX_OFFSET_ZX7     2176

long parse_long(char *str) {
    long value;

    errno = 0;
    value = strtol(str, NULL, 10);
    return !errno ? value : LONG_MIN;
}

void reverse(unsigned char *first, unsigned char *last) {
    unsigned char c;

    while (first < last) {
        c = *first;
        *first++ = *last;
        *last-- = c;
    }
}

int main(int argc, char *argv[]) {
    int skip = 0;
    int forced_mode = FALSE;
    int quick_mode = FALSE;
    int backwards_mode = FALSE;
    char *input_name;
    char *output_name;
    unsigned char *input_data;
    unsigned char *output_data;
    FILE *ifp;
    FILE *ofp;
    // size_t input_size;
    // size_t output_size;
    // size_t partial_counter;
    // size_t total_counter;
    // long delta;
    int input_size;
    int output_size;
    int partial_counter;
    int total_counter;
    int delta;
    int i;
    char loader_data[128];
    size_t loader_size;

    /* process hidden optional parameters */
    for (i = 1; i < argc && (*argv[i] == '-' || *argv[i] == '+'); i++) {
        if (!strcmp(argv[i], "-f")) {
            forced_mode = 1;
        } else if (!strcmp(argv[i], "-q")) {
            quick_mode = TRUE;
        } else if (!strcmp(argv[i], "-b")) {
            backwards_mode = 1;
        } else if ((skip = parse_long(argv[i])) <= 0) {
            fprintf(stderr, "Error: Invalid parameter %s\n", argv[i]);
            exit(1);
        }
    }

    /* determine output filename */
    if (argc == i+1) {
        input_name = argv[i];
        input_size = strlen(input_name);
        if (input_size > 4 && (!strcmp(input_name+input_size-4, ".mzf") ||
                               !strcmp(input_name+input_size-4, ".mzt"))) {
            output_name = (char *)malloc(input_size);
            strcpy(output_name, input_name);
            output_name[input_size-1] = quick_mode ? '7' : '0';
        } else {
            fprintf(stderr, "Error: Cannot infer input filename\n");
            exit(1);
        }
    } else if (argc == i+2) {
        output_name = argv[i+1];
    } else {
        fprintf(stderr, "mz0c: using optimal data compression by Einar Saukas\n");
        fprintf(stderr, "Usage: %s [-e] [-f] [-b] input.mzf [output.mz7]\n"
                        "  -f      Force overwrite of output file\n"
                        "  -b      Compress backwards\n"
                        "  -q      Quick non-optimal compression\n", argv[0]);
        exit(1);
    }

    /* open input file */
    ifp = fopen(argv[i], "rb");
    if (!ifp) {
        fprintf(stderr, "Error: Cannot access input file %s\n", argv[i]);
        exit(1);
    }

    /* determine input size */
    fseek(ifp, 0L, SEEK_END);
    input_size = ftell(ifp);
    fseek(ifp, 0L, SEEK_SET);
    if (!input_size || input_size <= 128) {
        fprintf(stderr, "Error: Empty input file %s\n", argv[i]);
        exit(1);
    }

    /* validate skip against input size */
    if (skip >= input_size) {
        fprintf(stderr, "Error: Skipping entire input file %s\n", argv[i]);
        exit(1);
    }

    /* allocate input buffer */
    input_data = (unsigned char *)malloc(input_size);
    if (!input_data) {
        fprintf(stderr, "Error: Insufficient memory\n");
        exit(1);
    }

    /* read input file */
    total_counter = 0;
    do {
        partial_counter = fread(input_data+total_counter, sizeof(char), input_size-total_counter, ifp);
        total_counter += partial_counter;
    } while (partial_counter > 0);

    if (total_counter != input_size) {
        fprintf(stderr, "Error: Cannot read input file %s\n", argv[i]);
        exit(1);
    }

    /* close input file */
    fclose(ifp);

    /* check output file */
    if (!forced_mode && fopen(output_name, "rb") != NULL) {
        fprintf(stderr, "Error: Already existing output file %s\n", output_name);
        exit(1);
    }

    /* create output file */
    ofp = fopen(output_name, "wb");
    if (!ofp) {
        fprintf(stderr, "Error: Cannot create output file %s\n", output_name);
        exit(1);
    }

    /* conditionally reverse input file */
    if (backwards_mode) {
        reverse(input_data+sizeof(Header), input_data+input_size-1);
    }

    /* generate output file */
    output_data = compress(optimize(input_data+sizeof(Header), input_size-sizeof(Header), skip, quick_mode ? MAX_OFFSET_ZX7 : MAX_OFFSET_ZX0), input_data+sizeof(Header), input_size-sizeof(Header), skip, backwards_mode, &output_size, &delta);

    /* conditionally reverse output file */
    if (backwards_mode) {
        reverse(output_data, output_data+output_size-1);
    }

    fill_header_and_loader((Header *)input_data, loader_data, &loader_size, skip, output_size, backwards_mode, delta);

    /* write output file */
    if (fwrite(input_data, sizeof(char), sizeof(Header), ofp) != sizeof(Header)) {
        fprintf(stderr, "Error: Cannot write output file %s\n", output_name);
        exit(1);
    }
    if (!backwards_mode && fwrite(loader_data, sizeof(char), loader_size, ofp) != loader_size) {
        fprintf(stderr, "Error: Cannot write output file %s\n", output_name);
        exit(1);
    }
    if (fwrite(output_data, sizeof(char), output_size, ofp) != output_size) {
        fprintf(stderr, "Error: Cannot write output file %s\n", output_name);
        exit(1);
    }
    if (backwards_mode && fwrite(loader_data, sizeof(char), loader_size, ofp) != loader_size) {
        fprintf(stderr, "Error: Cannot write output file %s\n", output_name);
        exit(1);
    }

    /* close output file */
    fclose(ofp);

    /* done! */
    printf("Data%s converted%s from %lu to %lu bytes! (delta %ld)\n", (skip ? " partially" : ""), (backwards_mode ? " backwards" : ""),
        (unsigned long)(input_size-skip-128), (unsigned long)output_size, delta);

    return 0;
}
