;;; rv.el - a RISC-V emulator              -*- lexical-binding: t; -*-

;; Copyright (C) 2023 defanor

;; Author: defanor <defanor@uberspace.net>
;; Maintainer: defanor <defanor@uberspace.net>
;; Created: 2023-12-20
;; Keywords: RISC-V, emulation, amusements
;; Homepage: https://git.uberspace.net/rv.el/
;; Version: 0.0.0

;; This file is not part of GNU Emacs.

;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; An incomplete and slow RISC-V emulator for Emacs. Meant and
;; published for fun, possibly as an educational project, not aiming
;; serious usage. For practical emulation, see QEMU. Targeting RV64GC
;; and Linux emulation for now.

;;; Code:

(defun rv-to-int (number width)
  "Convert a NUMBER read as an unsigned number of WIDTH bits to a
signed integer, assuming that it is encoded using two's
complement."
  (let ((sign-bit (ash number (- (- width 1)))))
    (logior (- (* sign-bit (expt 2 (- width 1))))
            (logand number (- (expt 2 width) 1)))))

(defun rv-from-int (integer width)
  "Convert an INTEGER to a signed number of WIDTH bits, encoded in
two's complement."
  (logand (- (expt 2 width) 1)
          (if (< integer 0)
              (+ (expt 2 width) integer)
            integer)))

(defun rv-sext (number width-from width-to)
  "Sign-extend a NUMBER encoded in two's complement from WIDTH-FROM
bits to WIDTH-TO bits."
  (let ((sign-bit (ash number (- (- width-from 1)))))
    (while (<= width-from width-to)
      (setq number (logior (ash sign-bit (- width-from 1)) number))
      (setq width-from (+ width-from 1)))
    number))

(defun rv-to-float (number width)
  "Decode an IEEE 754's binary<WIDTH> floating-point NUMBER."
  (let* ((significand-width (pcase width
                              (16 10)
                              (32 23)
                              (64 52)
                              (128 112)))
         (exponent-width (- width significand-width 1))
         (sign (ash number (- 1 width)))
         (exponent-bin (logand
                        (ash number (- significand-width))
                        (- (expt 2 exponent-width) 1)))
         (significand-bin (logand
                           number
                           (- (expt 2 significand-width) 1)))
         ;; Account for bias by 2^(exp_width - 1) - 1.
         (exponent-val (- exponent-bin
                          (- (expt 2 (- exponent-width 1)) 1)))
         (significand-val (+ 1 (/ (float significand-bin)
                                  (expt 2 significand-width)))))
    (* (expt -1 sign)
       (cond
        ((= exponent-bin 0) 0.0)
        ((= exponent-bin (- (expt 2 exponent-width) 1))
         (if (= significand-bin 0)
             1e+INF
           0e+NaN))
        (t (* (expt 2 exponent-val) significand-val))))))

(defun rv-from-float (num width)
  "Encode NUM as an IEEE 754's binary<WIDTH> floating-point
number."
  (let* ((number (float num))
         (significand-width (pcase width
                              (16 10)
                              (32 23)
                              (64 52)
                              (128 112)))
         (exponent-width (- width significand-width 1))
         (sign (if (= (copysign 1.0 (float number)) 1.0) 0 1))
         ;; Frexp returns a significand between 0.5 and 1, or 0.1 and
         ;; 1 in binary. Negative for negative numbers though.
         (significand-val (abs (car (frexp number))))
         (exponent-val (cdr (frexp number)))
         ;; The exponent value is stored biased by 2^(exp_width - 1) -
         ;; 1 (e.g., 1023 for binary64's 11-bit exponent). But we are
         ;; also adjusting the significand, multiplying it by 2, so
         ;; reducing exponent by 1.
         (exponent-bin
          (cond
           ((= number 0) 0)
           ((isnan number) (- (expt 2 exponent-width) 1))
           ((= (abs number) 1.0e+INF) (- (expt 2 exponent-width) 1))
           (t (+ exponent-val
                 -1
                 (- (expt 2 (- exponent-width 1)) 1)))))
         ;; The significand value is the fractional part of a number
         ;; between 1 decimal (1 binary) and 2 decimal (10 binary),
         ;; while frexp returns one between 0.5 decimal (0.1 binary)
         ;; and 1 decimal (1 binary). Multiplying it by 2 and
         ;; subtracting 1 here, then extracting the fractional part
         ;; by multiplying to the whole width.
         (significand-bin
          (cond
           ((= significand-val 0) 0)
           ((isnan number) (- (expt 2 significand-width) 1))
           ((= (abs number) 1.0e+INF) 0)
           (t (truncate (* (- (* significand-val 2) 1)
                           (expt 2 significand-width)))))))
    (logior
     (ash sign (- width 1))
     (ash exponent-bin significand-width)
     significand-bin)))

(defun rv-bits (number lower len &optional xlen)
  "Extract LEN bits from a NUMBER, starting from LOWER bit."
  (unless xlen
    (setq xlen 64))
  (logand (ash number (- lower))
          (ash (1- (expt 2 xlen)) (- (- xlen len)))))

(defun rv-map-find (st position)
  "Find a page for a given POSITION in bytes."
  (cond ((vectorp st) (cons 0 st))
        ((consp st)
         (or (seq-find
              (lambda (m) (and (<= (car m) position)
                               (> (+ (car m) (length (cdr m))) position)))
              (cdr (assq 'mem st)))
             (and (message
                   "Failed to find a memory map for position %d (0x%X): %s"
                   position position
                   (mapcar (lambda (x) (cons (car x) (length (cdr x))))
                           (cdr (assq 'mem st))))
                  nil)))))

(defun rv-map-find-free (st len &optional after)
  "Find free space in a memory map, for a page of a given LEN"
  (let ((mem-chunks (seq-sort (lambda (x y) (< (car x) (car y)))
                              (cdr (assq 'mem st))))
        (start (or after #xf00d0000))
        (n 0))
    (while (not (or (null (seq-elt mem-chunks n))
                    (< (+ start len) (car (seq-elt mem-chunks n)))))
      (setq start (max start
                       (+ (car (seq-elt mem-chunks n))
                          (length (cdr (seq-elt mem-chunks n)))))
            n (+ n 1)))
    start))

(defun rv-read-byte (st position)
  "Read a single byte at POISITION."
  (let ((mem-map (rv-map-find st position)))
    (when mem-map
      (seq-elt (cdr mem-map) (- position (car mem-map))))))

(defun rv-write-byte (st position val)
  "Write a single byte, VAL, into POSITION of memory map MEM."
  (let ((mem-map (rv-map-find st position)))
    (when mem-map
      (aset (cdr mem-map)
            (- position (car mem-map))
            val))))

(defun rv-read-num (st start len &optional big-endian)
  "Read a number at START position, of a given LEN in bytes."
  (let ((n 0)
        (r 0))
    (while (and r (< n len))
      (let ((b (rv-read-byte st (+ start (if big-endian n (- len n 1))))))
        (if b
            (setq r (logior (ash r 8) b)
                  n (1+ n))
          (progn
            (message "Failed to read a number of length %d at %d (0x%X)"
                     len start start)
            (setq r nil)))))
    r))

(defun rv-write-num (st val start len &optional big-endian)
  "Write a number into the START position, of a given LEN in
bytes."
  (let ((n 0)
        (r st))
    (while (and r (< n len))
      (if (rv-write-byte st
                         (+ start (if big-endian (- len n 1) n))
                         (logand val #xFF))
        (setq val (ash val -8)
              n (1+ n))
        (setq r nil))
      )
    r))

(defun rv-read-string (st start &optional len)
  "Read a string starting at START. Of a fixed length, if LEN is
provided, or zero-terminated."
  (let ((mem-map (rv-map-find st start)))
    (when mem-map
      (unless len
        (setq len 0)
        (while (and (rv-read-byte st (+ start len))
                    (> (rv-read-byte st (+ start len)) 0))
          (setq len (+ len 1))))
      (let ((rel-pos (- start (car mem-map))))
        (seq-into (seq-subseq (cdr mem-map) rel-pos (+ rel-pos len))
                  'string)))))

(defun rv-write-string (st val start)
  "Write a string into a given memory location."
  (seq-map-indexed (lambda (elt idx)
                     (rv-write-byte st (+ start idx) elt)
                     st)
                   val))

(defun rv-load-file (fn)
  "Read file FN, returning it as a vector of bytes."
  (with-current-buffer (find-file-noselect fn nil t)
    (string-to-vector (buffer-substring-no-properties (point-min) (point-max)))))

(defun rv-xr (state n)
  "Read from integer register N."
  (if (eq n 0)
      0
    (seq-elt (cdr (assq 'r state)) n)))

(defun rv-xw (state n value)
  "Write VALUE into integer register N."
  (unless (eq n 0)
    (aset (cdr (assq 'r state)) n value)))

(defun rv-fr (state n)
  "Read from floating-point register N."
  (seq-elt (cdr (assq 'f state)) n))

(defun rv-fw (state n value)
  "Write VALUE into floating-point register N."
  (aset (cdr (assq 'f state)) n value))

(setq rv-standard-fields
      '((rd . 5)
        (rs1 . 5)
        (rs2 . 5)
        (rs3 . 5)
        (rm . 3)
        (rd-short . 3)
        (rs1-short . 3)
        (rs2-short . 3)
        (funct3 . 3)
        (funct7 . 7)
        (csr . 12)
        ))

(defun rv-instructions (&optional _xlen)
  `((RV32I
     (LUI    (imm (31 . 12)) rd #b0110111)
     (AUIPC  (imm (31 . 12)) rd #b0010111)
     (JAL    (imm 20 (10 . 1) 11 (19 . 12)) rd #b1101111)
     (JALR   (imm (11 . 0)) rs1 (#b000 . 3) rd #b1100111)
     (BEQ    (imm 12 (10 . 5)) rs2 rs1 (#b000 . 3) (imm (4 . 1) 11) #b1100011)
     (BNE    (imm 12 (10 . 5)) rs2 rs1 (#b001 . 3) (imm (4 . 1) 11) #b1100011)
     (BLT    (imm 12 (10 . 5)) rs2 rs1 (#b100 . 3) (imm (4 . 1) 11) #b1100011)
     (BGE    (imm 12 (10 . 5)) rs2 rs1 (#b101 . 3) (imm (4 . 1) 11) #b1100011)
     (BLTU   (imm 12 (10 . 5)) rs2 rs1 (#b110 . 3) (imm (4 . 1) 11) #b1100011)
     (BGEU   (imm 12 (10 . 5)) rs2 rs1 (#b111 . 3) (imm (4 . 1) 11) #b1100011)
     (LB     (imm (11 . 0)) rs1 (#b000 . 3) rd #b0000011)
     (LH     (imm (11 . 0)) rs1 (#b001 . 3) rd #b0000011)
     (LW     (imm (11 . 0)) rs1 (#b010 . 3) rd #b0000011)
     (LBU    (imm (11 . 0)) rs1 (#b100 . 3) rd #b0000011)
     (LHU    (imm (11 . 0)) rs1 (#b101 . 3) rd #b0000011)
     (SB     (imm (11 . 5)) rs2 rs1 (#b000 . 3) (imm (4 . 0)) #b0100011)
     (SH     (imm (11 . 5)) rs2 rs1 (#b001 . 3) (imm (4 . 0)) #b0100011)
     (SW     (imm (11 . 5)) rs2 rs1 (#b010 . 3) (imm (4 . 0)) #b0100011)
     (ADDI   (imm (11 . 0)) rs1 (#b000 . 3) rd #b0010011)
     (SLTI   (imm (11 . 0)) rs1 (#b010 . 3) rd #b0010011)
     (SLTIU  (imm (11 . 0)) rs1 (#b011 . 3) rd #b0010011)
     (XORI   (imm (11 . 0)) rs1 (#b100 . 3) rd #b0010011)
     (ORI    (imm (11 . 0)) rs1 (#b110 . 3) rd #b0010011)
     (ANDI   (imm (11 . 0)) rs1 (#b111 . 3) rd #b0010011)
     (SLLI   (#b0000000 . 7) (shamt (4 . 0)) rs1 (#b001 . 3) rd #b0010011)
     (SRLI   (#b0000000 . 7) (shamt (4 . 0)) rs1 (#b101 . 3) rd #b0010011)
     (SRAI   (#b0100000 . 7) (shamt (4 . 0)) rs1 (#b101 . 3) rd #b0010011)
     (ADD    (#b0000000 . 7) rs2 rs1 (#b000 . 3) rd #b0110011)
     (SUB    (#b0100000 . 7) rs2 rs1 (#b000 . 3) rd #b0110011)
     (SLL    (#b0000000 . 7) rs2 rs1 (#b001 . 3) rd #b0110011)
     (SLT    (#b0000000 . 7) rs2 rs1 (#b010 . 3) rd #b0110011)
     (SLTU   (#b0000000 . 7) rs2 rs1 (#b011 . 3) rd #b0110011)
     (XOR    (#b0000000 . 7) rs2 rs1 (#b100 . 3) rd #b0110011)
     (SRL    (#b0000000 . 7) rs2 rs1 (#b101 . 3) rd #b0110011)
     (SRA    (#b0100000 . 7) rs2 rs1 (#b101 . 3) rd #b0110011)
     (OR     (#b0000000 . 7) rs2 rs1 (#b110 . 3) rd #b0110011)
     (AND    (#b0000000 . 7) rs2 rs1 (#b111 . 3) rd #b0110011)
     (FENCE  (fm (3 . 0)) (pred (3 . 0)) (succ (3 . 0)) rs1 (#b000 . 3) rd #b0001111)
     (ECALL  (0 . 12) (0 . 5) (0 . 3) (0 . 5) #b1110011)
     (EBREAK (1 . 12) (0 . 5) (0 . 3) (0 . 5) #b1110011))
    (RV64I
     (LWU    (imm (11 . 0)) rs1 (#b110 . 3) rd #b0000011)
     (LD     (imm (11 . 0)) rs1 (#b011 . 3) rd #b0000011)
     (SD     (imm (11 . 5)) rs2 rs1 (#b011 . 3) (imm (4 . 0)) #b0100011)
     (SLLI   (#b000000 . 6) (shamt (5 . 0)) rs1 (#b001 . 3) rd #b0010011)
     (SRLI   (#b000000 . 6) (shamt (5 . 0)) rs1 (#b101 . 3) rd #b0010011)
     (SRAI   (#b010000 . 6) (shamt (5 . 0)) rs1 (#b101 . 3) rd #b0010011)
     (ADDIW  (imm (11 . 0)) rs1 (#b000 . 3) rd #b0011011)
     (SLLIW  (#b0000000 . 7) (shamt (4 . 0)) rs1 (#b001 . 3) rd #b0011011)
     (SRLIW  (#b0000000 . 7) (shamt (4 . 0)) rs1 (#b101 . 3) rd #b0011011)
     (SRAIW  (#b0100000 . 7) (shamt (4 . 0)) rs1 (#b101 . 3) rd #b0011011)
     (ADDW   (#b0000000 . 7) rs2 rs1 (#b000 . 3) rd #b0111011)
     (SUBW   (#b0100000 . 7) rs2 rs1 (#b000 . 3) rd #b0111011)
     (SLLW   (#b0000000 . 7) rs2 rs1 (#b001 . 3) rd #b0111011)
     (SRLW   (#b0000000 . 7) rs2 rs1 (#b101 . 3) rd #b0111011)
     (SRAW   (#b0100000 . 7) rs2 rs1 (#b101 . 3) rd #b0111011))
    (RVC
     (Illegal    0)
     (C.ADDI4SPN (#b000 . 3) (nzuimm (5 . 4) (9 . 6) 2 3) rd-short #b00)
     (C.FLD      (#b001 . 3) (uimm (5 . 3)) rs1-short (uimm (7 . 6)) rd-short #b00)
     ;; (C.LQ       (#b001 . 3) (uimm (5 . 4) 8) rs1-short (uimm (7 . 6)) rd-short #b00)
     (C.LW       (#b010 . 3) (uimm (5 . 3)) rs1-short (uimm 2 6) rd-short #b00)
     ;; (C.FLW      (#b011 . 3) (uimm (5 . 3)) rs1-short (uimm 2 6) rd-short #b00)
     (C.LD       (#b011 . 3) (uimm (5 . 3)) rs1-short (uimm (7 . 6)) rd-short #b00)
     (Reserved   (#b100 . 3) (- (10 . 0)) #b00)
     (C.FSD      (#b101 . 3) (uimm (5 . 3)) rs1-short (uimm (7 . 6)) rs2-short #b00)
     ;; (C.SQ       (#b101 . 3) (uimm (5 . 4) 8) rs1-short (uimm (7 . 6)) rs2-short #b00)
     (C.SW       (#b110 . 3) (uimm (5 . 3)) rs1-short (uimm 2 6) rs2-short #b00)
     ;; (C.FSW      (#b111 . 3) (uimm (5 . 3)) rs1-short (uimm 2 6) rs2-short #b00)
     (C.SD       (#b111 . 3) (uimm (5 . 3)) rs1-short (uimm (7 . 6)) rs2-short #b00)
     (C.NOP      (#b000 . 3) (nzimm 5) (0 . 5) (nzimm (4 . 0)) #b01)
     (C.ADDI     (#b000 . 3) (nzimm 5) rs1 (nzimm (4 . 0)) #b01)
     ;; (C.JAL      (#b001 . 3) (imm 11 4 (9 . 8) 10 6 7 (3 . 1) 5) #b01)
     (C.ADDIW    (#b001 . 3) (imm 5) rs1 (imm (4 . 0)) #b01)
     (C.LI       (#b010 . 3) (imm 5) rd (imm (4 . 0)) #b01)
     (C.ADDI16SP (#b011 . 3) (nzimm 9) (2 . 5) (nzimm 4 6 (8 . 7) 5) #b01)
     (C.LUI      (#b011 . 3) (nzimm 17) rd (nzimm (16 . 12)) #b01)
     (C.SRLI     (#b100 . 3) (nzuimm 5) (#b00 . 2) rs1-short (nzuimm (4 . 0)) #b01)
     ;; (C.SRLI64   (#b100 . 3) (0 . 1) (#b00 . 2) rs1-short (0 . 5) #b01)
     (C.SRAI     (#b100 . 3) (nzuimm 5) (#b01 . 2) rs1-short (nzuimm (4 . 0)) #b01)
     ;; (C.SRAI64   (#b100 . 3) (0 . 1) (#b01 . 2) rs1-short (0 . 5) #b01)
     (C.ANDI     (#b100 . 3) (imm 5) (#b10 . 2) rs1-short (imm (4 . 0)) #b01)
     (C.SUB      (#b100011 . 6) rs1-short (#b00 . 2) rs2-short #b01)
     (C.XOR      (#b100011 . 6) rs1-short (#b01 . 2) rs2-short #b01)
     (C.OR       (#b100011 . 6) rs1-short (#b10 . 2) rs2-short #b01)
     (C.AND      (#b100011 . 6) rs1-short (#b11 . 2) rs2-short #b01)
     (C.SUBW     (#b100111 . 6) rs1-short (#b00 . 2) rs2-short #b01)
     (C.ADDW     (#b100111 . 6) rs1-short (#b01 . 2) rs2-short #b01)
     (Reserved   (#b100111 . 6) rs1-short (#b10 . 2) rs2-short #b01)
     (Reserved   (#b100111 . 6) rs1-short (#b11 . 2) rs2-short #b01)
     (C.J        (#b101 . 3) (imm 11 4 (9 . 8) 10 6 7 (3 . 1) 5) #b01)
     (C.BEQZ     (#b110 . 3) (imm 8 (4 . 3)) rs1-short (imm (7 . 6) (2 . 1) 5) #b01)
     (C.BNEZ     (#b111 . 3) (imm 8 (4 . 3)) rs1-short (imm (7 . 6) (2 . 1) 5) #b01)
     (C.SLLI     (#b000 . 3) (nzuimm 5) rs1 (nzuimm (4 . 0)) #b10)
     (C.SLLI64   (#b000 . 3) (0 . 1) rs1 (0 . 5) #b10)
     (C.FLDSP    (#b001 . 3) (uimm 5) rd (uimm (4 . 3) (8 . 6)) #b10)
     ;; (C.LQSP     (#b001 . 3) (uimm 5) rd (uimm 4 (9 . 6)) #b10)
     (C.LWSP     (#b010 . 3) (uimm 5) rd (uimm (4 . 2) (7 . 6)) #b10)
     ;; (C.FLWSP    (#b011 . 3) (uimm 5) rd (uimm (4 . 2) (7 . 6)) #b10)
     (C.LDSP     (#b011 . 3) (uimm 5) rd (uimm (4 . 3) (8 . 6)) #b10)
     (C.JR       (#b100 . 3) (0 . 1) rs1 (0 . 5) #b10)
     (C.MV       (#b100 . 3) (0 . 1) rd rs2 #b10)
     (C.EBREAK   (#b100 . 3) (1 . 1) (0 . 5) (0 . 5) #b10)
     (C.JALR     (#b100 . 3) (1 . 1) rs1 (0 . 5) #b10)
     (C.ADD      (#b100 . 3) (1 . 1) rs1 rs2 #b10)
     (C.FSDSP    (#b101 . 3) (uimm (5 . 3) (8 . 6)) rs2 #b10)
     ;; (C.SQSP     (#b101 . 3) (uimm (5 . 4) (9 . 6)) rs2 #b10)
     (C.SWSP     (#b110 . 3) (uimm (5 . 2) (7 . 6)) rs2 #b10)
     ;; (C.FSWSP    (#b111 . 3) (uimm (5 . 2) (7 . 6)) rs2 #b10)
     (C.SDSP     (#b111 . 3) (uimm (5 . 3) (8 . 6)) rs2 #b10)
     )
    (Zifencei
     (FENCE.I (imm (11 . 0)) rs1 (#b001 . 3) rd #b0001111))
    (Zicsr
     (CSRRW  csr rs1 (#b001 . 3) rd #b1110011)
     (CSRRS  csr rs1 (#b010 . 3) rd #b1110011)
     (CSRRC  csr rs1 (#b011 . 3) rd #b1110011)
     (CSRRWI csr (uimm 5) (#b101 . 3) rd #b1110011)
     (CSRRSI csr (uimm 5) (#b110 . 3) rd #b1110011)
     (CSRRCI csr (uimm 5) (#b111 . 3) rd #b1110011))
    (RV32M
     (MUL    (1 . 7) rs2 rs1 (#b000 . 3) rd #b0110011)
     (MULH   (1 . 7) rs2 rs1 (#b001 . 3) rd #b0110011)
     (MULHSU (1 . 7) rs2 rs1 (#b010 . 3) rd #b0110011)
     (MULHU  (1 . 7) rs2 rs1 (#b011 . 3) rd #b0110011)
     (DIV    (1 . 7) rs2 rs1 (#b100 . 3) rd #b0110011)
     (DIVU   (1 . 7) rs2 rs1 (#b101 . 3) rd #b0110011)
     (REM    (1 . 7) rs2 rs1 (#b110 . 3) rd #b0110011)
     (REMU   (1 . 7) rs2 rs1 (#b111 . 3) rd #b0110011))
    (RV64M
     (MULW   (1 . 7) rs2 rs1 (#b000 . 3) rd #b0111011)
     (DIVW   (1 . 7) rs2 rs1 (#b100 . 3) rd #b0111011)
     (DIVUW  (1 . 7) rs2 rs1 (#b101 . 3) rd #b0111011)
     (REMW   (1 . 7) rs2 rs1 (#b110 . 3) rd #b0111011)
     (REMUW  (1 . 7) rs2 rs1 (#b111 . 3) rd #b0111011))
    (RV32A
     (LR.W      (#b00010 . 5) (aq 0) (rl 0) (0 . 5) rs1 (#b010 . 3) rd #b0101111)
     (SC.W      (#b00011 . 5) (aq 0) (rl 0) rs2 rs1 (#b010 . 3) rd #b0101111)
     (AMOSWAP.W (#b00001 . 5) (aq 0) (rl 0) rs2 rs1 (#b010 . 3) rd #b0101111)
     (AMOADD.W  (#b00000 . 5) (aq 0) (rl 0) rs2 rs1 (#b010 . 3) rd #b0101111)
     (AMOXOR.W  (#b00100 . 5) (aq 0) (rl 0) rs2 rs1 (#b010 . 3) rd #b0101111)
     (AMOAND.W  (#b01100 . 5) (aq 0) (rl 0) rs2 rs1 (#b010 . 3) rd #b0101111)
     (AMOOR.W   (#b01000 . 5) (aq 0) (rl 0) rs2 rs1 (#b010 . 3) rd #b0101111)
     (AMOMIN.W  (#b10000 . 5) (aq 0) (rl 0) rs2 rs1 (#b010 . 3) rd #b0101111)
     (AMOMAX.W  (#b10100 . 5) (aq 0) (rl 0) rs2 rs1 (#b010 . 3) rd #b0101111)
     (AMOMINU.W (#b11000 . 5) (aq 0) (rl 0) rs2 rs1 (#b010 . 3) rd #b0101111)
     (AMOMAXU.W (#b11100 . 5) (aq 0) (rl 0) rs2 rs1 (#b010 . 3) rd #b0101111))
    (RV64A
     (LR.D      (#b00010 . 5) (aq 0) (rl 0) (0 . 5) rs1 (#b011 . 3) rd #b0101111)
     (SC.D      (#b00011 . 5) (aq 0) (rl 0) rs2 rs1 (#b011 . 3) rd #b0101111)
     (AMOSWAP.D (#b00001 . 5) (aq 0) (rl 0) rs2 rs1 (#b011 . 3) rd #b0101111)
     (AMOADD.D  (#b00000 . 5) (aq 0) (rl 0) rs2 rs1 (#b011 . 3) rd #b0101111)
     (AMOXOR.D  (#b00100 . 5) (aq 0) (rl 0) rs2 rs1 (#b011 . 3) rd #b0101111)
     (AMOAND.D  (#b01100 . 5) (aq 0) (rl 0) rs2 rs1 (#b011 . 3) rd #b0101111)
     (AMOOR.D   (#b01000 . 5) (aq 0) (rl 0) rs2 rs1 (#b011 . 3) rd #b0101111)
     (AMOMIN.D  (#b10000 . 5) (aq 0) (rl 0) rs2 rs1 (#b011 . 3) rd #b0101111)
     (AMOMAX.D  (#b10100 . 5) (aq 0) (rl 0) rs2 rs1 (#b011 . 3) rd #b0101111)
     (AMOMINU.D (#b11000 . 5) (aq 0) (rl 0) rs2 rs1 (#b011 . 3) rd #b0101111)
     (AMOMAXU.D (#b11100 . 5) (aq 0) (rl 0) rs2 rs1 (#b011 . 3) rd #b0101111))
    (RV32F
     (FLW       (imm (11 . 0)) rs1 (#b010 . 3) rd #b0000111)
     (FSW       (imm (11 . 5)) rs2 rs1 (#b010 . 3) (imm (4 . 0)) #b0100111)
     (FMADD.S   rs3 (#b00 . 2) rs2 rs1 rm rd #b1000011)
     (FMSUB.S   rs3 (#b00 . 2) rs2 rs1 rm rd #b1000111)
     (FNMSUB.S  rs3 (#b00 . 2) rs2 rs1 rm rd #b1001011)
     (FNMADD.S  rs3 (#b00 . 2) rs2 rs1 rm rd #b1001111)
     (FADD.S    (#b0000000 . 7) rs2 rs1 rm rd #b1010011)
     (FSUB.S    (#b0000100 . 7) rs2 rs1 rm rd #b1010011)
     (FMUL.S    (#b0001000 . 7) rs2 rs1 rm rd #b1010011)
     (FDIV.S    (#b0001100 . 7) rs2 rs1 rm rd #b1010011)
     (FSQRT.S   (#b0101100 . 7) (0 . 5) rs1 rm rd #b1010011)
     (FSGNJ.S   (#b0010000 . 7) rs2 rs1 (#b000 . 3) rd #b1010011)
     (FSGNJN.S  (#b0010000 . 7) rs2 rs1 (#b001 . 3) rd #b1010011)
     (FSGNJX.S  (#b0010000 . 7) rs2 rs1 (#b010 . 3) rd #b1010011)
     (FMIN.S    (#b0010100 . 7) rs2 rs1 (#b000 . 3) rd #b1010011)
     (FMAX.S    (#b0010100 . 7) rs2 rs1 (#b001 . 3) rd #b1010011)
     (FCVT.W.S  (#b1100000 . 7) (#b00000 . 5) rs1 rm rd #b1010011)
     (FCVT.WU.S (#b1100000 . 7) (#b00001 . 5) rs1 rm rd #b1010011)
     (FMV.X.W   (#b1110000 . 7) (#b00000 . 5) rs1 (#b000 . 3) rd #b1010011)
     (FEQ.S     (#b1010000 . 7) rs2 rs1 (#b010 . 3) rd #b1010011)
     (FLT.S     (#b1010000 . 7) rs2 rs1 (#b001 . 3) rd #b1010011)
     (FLE.S     (#b1010000 . 7) rs2 rs1 (#b000 . 3) rd #b1010011)
     (FCLASS.S  (#b1110000 . 7) (#b00000 . 5) rs1 (#b001 . 3) rd #b1010011)
     (FCVT.S.W  (#b1101000 . 7) (#b00000 . 5) rs1 rm rd #b1010011)
     (FCVT.S.WU (#b1101000 . 7) (#b00001 . 5) rs1 rm rd #b1010011)
     (FMV.W.X   (#b1111000 . 7) (#b00000 . 5) rs1 (#b000 . 3) rd #b1010011))
    (RV64F
     (FCVT.L.S  (#b1100000 . 7) (#b00010 . 5) rs1 rm rd #b1010011)
     (FCVT.LU.S (#b1100000 . 7) (#b00011 . 5) rs1 rm rd #b1010011)
     (FCVT.S.L  (#b1101000 . 7) (#b00010 . 5) rs1 rm rd #b1010011)
     (FCVT.S.LU (#b1101000 . 7) (#b00011 . 5) rs1 rm rd #b1010011))
    (RV32D
     (FLD       (imm (11 . 0)) rs1 (#b011 . 3) rd #b0000111)
     (FSD       (imm (11 . 5)) rs2 rs1 (#b011 . 3) (imm (4 . 0)) #b0100111)
     (FMADD.D   rs3 (#b01 . 2) rs2 rs1 rm rd #b1000011)
     (FMSUB.D   rs3 (#b01 . 2) rs2 rs1 rm rd #b1000111)
     (FNMSUB.D  rs3 (#b01 . 2) rs2 rs1 rm rd #b1001011)
     (FNMADD.D  rs3 (#b01 . 2) rs2 rs1 rm rd #b1001111)
     (FADD.D    (#b0000001 . 7) rs2 rs1 rm rd #b1010011)
     (FSUB.D    (#b0000101 . 7) rs2 rs1 rm rd #b1010011)
     (FMUL.D    (#b0001001 . 7) rs2 rs1 rm rd #b1010011)
     (FDIV.D    (#b0001101 . 7) rs2 rs1 rm rd #b1010011)
     (FSQRT.D   (#b0101101 . 7) (#b00000 . 5) rs1 rm rd #b1010011)
     (FSGNJ.D   (#b0010001 . 7) rs2 rs1 (#b000 . 3) rd #b1010011)
     (FSGNJN.D  (#b0010001 . 7) rs2 rs1 (#b001 . 3) rd #b1010011)
     (FSGNJX.D  (#b0010001 . 7) rs2 rs1 (#b010 . 3) rd #b1010011)
     (FSMIN.D   (#b0010101 . 7) rs2 rs1 (#b000 . 3) rd #b1010011)
     (FSMAX.D   (#b0010101 . 7) rs2 rs1 (#b001 . 3) rd #b1010011)
     (FCVT.S.D  (#b0100000 . 7) (#b00001 . 5) rs1 rm rd #b1010011)
     (FCVT.D.S  (#b0100001 . 7) (#b00000 . 5) rs1 rm rd #b1010011)
     (FEQ.D     (#b1010001 . 7) rs2 rs1 (#b010 . 3) rd #b1010011)
     (FLT.D     (#b1010001 . 7) rs2 rs1 (#b001 . 3) rd #b1010011)
     (FLE.D     (#b1010001 . 7) rs2 rs1 (#b000 . 3) rd #b1010011)
     (FCLASS.D  (#b1110001 . 7) (#b00000 . 5) rs1 (#b001 . 3) rd #b1010011)
     (FCVT.W.D  (#b1100001 . 7) (#b00000 . 5) rs1 rm rd #b1010011)
     (FCVT.WU.D (#b1100001 . 7) (#b00001 . 5) rs1 rm rd #b1010011)
     (FCVT.D.W  (#b1101001 . 7) (#b00000 . 5) rs1 rm rd #b1010011)
     (FCVT.D.WU (#b1101001 . 7) (#b00001 . 5) rs1 rm rd #b1010011))
    (RV64D
     (FCVT.L.D  (#b1100001 . 7) (#b00010 . 5) rs1 rm rd #b1010011)
     (FCVT.LU.D (#b1100001 . 7) (#b00011 . 5) rs1 rm rd #b1010011)
     (FMV.X.D   (#b1110001 . 7) (#b00000 . 5) rs1 (#b000 . 3) rd #b1010011)
     (FCVT.D.L  (#b1101001 . 7) (#b00010 . 5) rs1 rm rd #b1010011)
     (FCVT.D.LU (#b1101001 . 7) (#b00011 . 5) rs1 rm rd #b1010011)
     (FMV.D.X   (#b1111001 . 7) (#b00000 . 5) rs1 (#b000 . 3) rd #b1010011))
    ;; TODO: Q
    (Privileged
     (SRET            (#b0001000 . 7) (#b00010 . 5) (#b00000 . 5) (#b000 . 3)
                      (#b00000 . 5) #b1110011)
     (MRET            (#b0011000 . 7) (#b00010 . 5) (#b00000 . 5) (#b000 . 3)
                      (#b00000 . 5) #b1110011)
     (WFI             (#b0001000 . 7) (#b00101 . 5) (#b00000 . 5) (#b000 . 3)
                      (#b00000 . 5) #b1110011)
     (SFENCE.VMA      (#b0001001 . 7) rs2 rs1 (#b000 . 3) (#b00000 . 5) #b1110011)
     (SINVAL.VMA      (#b0001011 . 7) rs2 rs1 (#b000 . 3) (#b00000 . 5) #b1110011)
     (SFENCE.W.INVAL  (#b0001100 . 7) (#b00000 . 5) (#b00000 . 5) (#b000 . 3)
                      (#b00000 . 5) #b1110011)
     (SFENCE.INVAL.IR (#b0001100 . 7) (#b00001 . 5) (#b00000 . 5) (#b000 . 3)
                      (#b00000 . 5) #b1110011)
     (HFENCE.VVMA     (#b0010001 . 7) rs2 rs1 (#b000 . 3) (#b00000 . 5) #b1110011)
     (HFENCE.GVMA     (#b0110001 . 7) rs2 rs1 (#b000 . 3) (#b00000 . 5) #b1110011)
     (HINVAL.VVMA     (#b0010011 . 7) rs2 rs1 (#b000 . 3) (#b00000 . 5) #b1110011)
     (HINVAL.GVMA     (#b0110011 . 7) rs2 rs1 (#b000 . 3) (#b00000 . 5) #b1110011)
     (HLV.B           (#b0110000 . 7) (#b00000 . 5) rs1 (#b100 . 3) rd #b1110011)
     (HLV.BU          (#b0110000 . 7) (#b00001 . 5) rs1 (#b100 . 3) rd #b1110011)
     (HLV.H           (#b0110010 . 7) (#b00000 . 5) rs1 (#b100 . 3) rd #b1110011)
     (HLV.HU          (#b0110010 . 7) (#b00001 . 5) rs1 (#b100 . 3) rd #b1110011)
     (HLVX.HU         (#b0110010 . 7) (#b00011 . 5) rs1 (#b100 . 3) rd #b1110011)
     (HLV.W           (#b0110100 . 7) (#b00000 . 5) rs1 (#b100 . 3) rd #b1110011)
     (HLVX.WWU        (#b0110100 . 7) (#b00011 . 5) rs1 (#b100 . 3) rd #b1110011)
     (HSV.B           (#b0110001 . 7) rs2 rs1 (#b100 . 3) (#b00000 . 5) #b1110011)
     (HSV.H           (#b0110011 . 7) rs2 rs1 (#b100 . 3) (#b00000 . 5) #b1110011)
     (HSV.W           (#b0110101 . 7) rs2 rs1 (#b100 . 3) (#b00000 . 5) #b1110011)
     (HLV.WU          (#b0110100 . 7) (#b00001 . 5) rs1 (#b100 . 3) rd #b1110011)
     (HLV.D           (#b0110110 . 7) (#b00000 . 5) rs1 (#b100 . 3) rd #b1110011)
     (HLV.W           (#b0110111 . 7) rs2 rs1 (#b100 . 3) (#b00000 . 5) #b1110011))))

(setq rv-opcode-instructions
      (let ((r (make-hash-table))
            (all-instructions (rv-instructions)))
        (while all-instructions
          (let* ((cur-ext (car all-instructions))
                 (ext-name (car cur-ext))
                 (ext-instructions (cdr cur-ext)))
            (while ext-instructions
              (let* ((cur-instruction (car ext-instructions))
                     (cur-opcode (car (last cur-instruction)))
                     (new-entry (cons ext-name cur-instruction))
                     (cur-val (gethash cur-opcode r)))
                (puthash cur-opcode
                         ;; Keep the order, since it is important: put
                         ;; the instruction into the end.
                         (append cur-val (list new-entry))
                         r))
              (setq ext-instructions (cdr ext-instructions))))
          (setq all-instructions (cdr all-instructions)))
        r))

(defun rv-encode (instruction extensions &optional xlen)
  "Encode an instruction provided as an S-expression, into a
number. Since certain instructions are present in different
extensions, a list of extensions is accepted as an argument to
set their priorities: those found earlier in the list have a
higher priority."
  (let ((all-instructions (rv-instructions xlen))
        (ret 0))
    (while (and extensions (= ret 0))
      (let* ((ext-instructions (cdr (assoc (car extensions) all-instructions)))
             (template (assoc (car instruction) ext-instructions)))
        (when template
          (let ((pos (if (eq (car extensions) 'RVC) 16 32)))
            (dolist (tmpl (cdr template))
              (cond
               ;; Standard named field
               ((symbolp tmpl)
                (setq pos (- pos (cdr (assoc tmpl rv-standard-fields))))
                (setq ret
                      (logior ret
                              (ash (cdr (assoc tmpl (cdr instruction)))
                                   pos))))
               ;; Opcode (similar to a constant, but without size)
               ((integerp tmpl)
                (setq ret (logior ret tmpl))
                (setq pos 0))
               ;; Constant
               ((and (consp tmpl) (integerp (car tmpl)))
                (setq pos (- pos (cdr tmpl)))
                (setq ret (logior ret (ash (car tmpl) pos))))
               ;; Non-standard named field
               ((and (consp tmpl) (symbolp (car tmpl)))
                (if (eq (car tmpl) 'check)
                    ;; A constraint (TODO)
                    nil
                  (dolist (range (cdr tmpl))
                    (when (integerp range)
                      (setq range (cons range range)))
                    (setq pos (- pos (- (car range) (cdr range)) 1))
                    (setq
                     ret
                     (logior
                      ret
                      (ash (rv-bits (cdr (assoc (car tmpl) (cdr instruction)))
                                    (cdr range)
                                    (+ (- (car range) (cdr range)) 1))
                           pos)
                      )))))
               )))))
      (setq extensions (cdr extensions)))
    ret))

(defun rv-decode-try (instruction template _xlen)
  "Try to decode an INSTRUCTION, using a given TEMPLATE."
  (let* ((pos (if (= (logand instruction #b11) #b11) 32 16))
         (name (car template))
         (r nil)
         (next-bits (lambda (n)
                      (setq pos (- pos n))
                      (rv-bits instruction pos n))))
    (setq template (cdr template))
    (while (and name template)
      (let ((tmpl (car template)))
        (cond
         ;; Standard named field
         ((symbolp tmpl)
          (push (cons tmpl
                      (funcall next-bits (cdr (assoc tmpl rv-standard-fields))))
                r))
         ;; Opcode (similar to a constant, but without size)
         ((integerp tmpl)
          (unless (= tmpl
                     (funcall next-bits pos))
            (setq name nil)))
         ;; Constant
         ((and (consp tmpl) (integerp (car tmpl)))
          (unless (= (car tmpl)
                     (funcall next-bits (cdr tmpl)))
            (setq name nil)))
         ;; Non-standard named field
         ((and (consp tmpl) (symbolp (car tmpl)))
          (if (eq (car tmpl) 'check)
              ;; A constraint
              (unless (eval (cdr tmpl))
                (setq name nil))
            (let ((val (or (cdr (assoc (car tmpl) r)) 0)))
              (dolist (range (cdr tmpl))
                (when (integerp range)
                  (setq range (cons range range)))
                (setq
                 val
                 (logior
                  val
                  (ash (funcall
                        next-bits
                        (+ (- (car range) (cdr range)) 1))
                       (cdr range)))))
              (push (cons (car tmpl) val) r))))))
      (setq template (cdr template)))
    (when name
      (cons name r))))

(defun rv-decode-slow (i &optional xlen)
  "Decode an instruction, using `rv-instructions' directly. For an
optimized version, see `rv-decode'."
  (let* ((all-extensions (rv-instructions (or xlen 64)))
         (result nil))
    (while (and all-extensions (not result))
      (let ((extension (car all-extensions)))
        (let ((template
               (seq-find (lambda (x) (rv-decode-try i x (or xlen 64)))
                         (cdr extension))))
          (when template
            (setq result (cons (car extension)
                               (rv-decode-try i template xlen))))))
      (setq all-extensions (cdr all-extensions)))
    result))

(defun rv-decode (i &optional xlen)
  "Decode an instruction I, represented as a number, into an
S-expression."
  (let* ((opcode (logand i (if (= (logand i #b11) #b11) #b1111111 #b11)))
         (candidates (gethash opcode rv-opcode-instructions))
         (result nil))
    (while (and candidates (not result))
      (let* ((cur-candidate (car candidates))
             (decoded (rv-decode-try i (cdr cur-candidate) (or xlen 64))))
        (when decoded
          (setq result (cons (car cur-candidate) decoded)))
        (setq candidates (cdr candidates))))
    result))

(defun rv-decompress (i)
  "Decompress an RVC instruction."
  (if (not (eq (car i) 'RVC))
      i
    (let* ((params (cddr i))
           (rd (cdr (assoc 'rd params)))
           (rs1 (cdr (assoc 'rs1 params)))
           (rs2 (cdr (assoc 'rs2 params)))
           (rd-short (cdr (assoc 'rd-short params)))
           (rs1-short (cdr (assoc 'rs1-short params)))
           (rs2-short (cdr (assoc 'rs2-short params)))
           (imm (cdr (assoc 'imm params)))
           (uimm (cdr (assoc 'uimm params)))
           (nzimm (cdr (assoc 'nzimm params)))
           (nzuimm (cdr (assoc 'nzuimm params))))
      (pcase (cadr i)
        ('C.ADDI4SPN
         `(RV32I ADDI (rd . ,(+ 8 rd-short)) (rs1 . 2) (imm . ,nzuimm)))
        ('C.FLD
         `(RV32I FLD (rd . ,(+ 8 rd-short)) (rs1 . ,(+ 8 rs1-short)) (imm . ,uimm)))
        ;; C.LQ (128)
        ('C.LW
         `(RV32I LW (rd . ,(+ 8 rd-short)) (rs1 . ,(+ 8 rs1-short)) (imm . ,uimm)))
        ;; ('C.FLW (32)
        ;;  `(RV32I FLW (rd . ,(+ 8 rd-short)) (rs1 . ,(+ 8 rs1-short)) (imm . ,uimm)))
        ('C.LD
         `(RV32I LD (rd . ,(+ 8 rd-short)) (rs1 . ,(+ 8 rs1-short)) (imm . ,uimm)))
        ;; Reserved
        ('C.FSD
         `(RV32D FSD (rs1 . ,(+ 8 rs1-short)) (rs2 . ,(+ 8 rs2-short))
                 (imm . ,uimm)))
        ;; C.SQ (128)
        ('C.SW
         `(RV32I SW (rs2 . ,(+ 8 rs2-short)) (rs1 . ,(+ 8 rs1-short))
                 (imm . ,uimm)))
        ;; C.FSW (32)
        ('C.SD
         `(RV32I SD (rs2 . ,(+ 8 rs2-short)) (rs1 . ,(+ 8 rs1-short))
                 (imm . ,uimm)))
        ('C.NOP
         `(RV32I ADDI (rd . 0) (rs1 . 0) (imm . 0)))
        ('C.ADDI
         `(RV32I ADDI (rd . ,rs1) (rs1 . ,rs1) (imm . ,(rv-sext nzimm 6 12))))
        ;; C.JAL (32)
        ('C.ADDIW
         `(RV32I ADDIW (rd . ,rs1) (rs1 . ,rs1) (imm . ,(rv-sext imm 6 12))))
        ('C.LI
         `(RV32I ADDI (rd . ,rd) (rs1 . 0) (imm . ,(rv-sext imm 6 12))))
        ('C.ADDI16SP
         `(RV32I ADDI (rd . 2) (rs1 . 2) (imm . ,(rv-sext nzimm 10 12))))
        ('C.LUI
         `(RV32I LUI (rd . ,rd) (imm . ,(rv-sext nzimm 18 32))))
        ('C.SRLI
         `(RV64I SRLI (rd . ,(+ 8 rs1-short)) (rs1 . ,(+ 8 rs1-short))
                 (shamt . ,nzuimm)))
        ;; C.SRLI64 (128)
        ('C.SRAI
         `(RV64I SRAI (rd . ,(+ 8 rs1-short)) (rs1 . ,(+ 8 rs1-short))
                 (shamt . ,nzuimm)))
        ;; C.SRAI64 (128)
        ('C.ANDI
         `(RV32I ANDI (rd . ,(+ 8 rs1-short)) (rs1 . ,(+ 8 rs1-short))
                 (imm . ,(rv-sext imm 6 12))))
        ('C.SUB
         `(RV32I SUB (rd . ,(+ 8 rs1-short)) (rs1 . ,(+ 8 rs1-short))
                 (rs2 . ,(+ 8 rs2-short))))
        ('C.XOR
         `(RV32I XOR (rd . ,(+ 8 rs1-short)) (rs1 . ,(+ 8 rs1-short))
                 (rs2 . ,(+ 8 rs2-short))))
        ('C.OR
         `(RV32I OR (rd . ,(+ 8 rs1-short)) (rs1 . ,(+ 8 rs1-short))
                 (rs2 . ,(+ 8 rs2-short))))
        ('C.AND
         `(RV32I AND (rd . ,(+ 8 rs1-short)) (rs1 . ,(+ 8 rs1-short))
                 (rs2 . ,(+ 8 rs2-short))))
        ('C.SUBW
         `(RV64I SUBW (rd . ,(+ 8 rs1-short)) (rs1 . ,(+ 8 rs1-short))
                 (rs2 . ,(+ 8 rs2-short))))
        ('C.ADDW
         `(RV64I ADDW (rd . ,(+ 8 rs1-short)) (rs1 . ,(+ 8 rs1-short))
                 (rs2 . ,(+ 8 rs2-short))))
        ;; Reserved * 2
        ('C.J
         `(RV32I JAL (rd . 0) (imm . ,(rv-sext imm 12 21))))
        ('C.BEQZ
         `(RV32I BEQ (rs1 . ,(+ 8 rs1-short)) (rs2 . 0) (imm . ,(rv-sext imm 9 13))))
        ('C.BNEZ
         `(RV32I BNE (rs1 . ,(+ 8 rs1-short)) (rs2 . 0) (imm . ,(rv-sext imm 9 13))))
        ('C.SLLI
         `(RV32I SLLI (rd . ,rs1) (rs1 . ,rs1) (shamt . ,nzuimm)))
        ;; C.SLLI64 (128)
        ('C.FLDSP
         `(RV32D FLD (rd . ,rd) (rs1 . 2) (imm . ,uimm)))
        ;; LQSP (128)
        ('C.LWSP
         `(RV32I LW (rd . ,rd) (rs1 . 2) (imm . ,uimm)))
        ;; C.FLWSP (32)
        ('C.LDSP
         `(RV64I LD (rd . ,rd) (rs1 . 2) (imm . ,uimm)))
        ('C.JR
         `(RV32I JALR (rd . 0) (rs1 . ,rs1) (imm . 0)))
        ('C.MV
         `(RV32I ADD (rd . ,rd) (rs1 . 0) (rs2 . ,rs2)))
        ('C.EBREAK
         '(RV32I EBREAK))
        ('C.JALR
         `(RV32I JALR (rd . 1) (rs1 . ,rs1) (imm . 0)))
        ('C.ADD
         `(RV32I ADD (rd . ,rs1) (rs1 . ,rs1) (rs2 . ,rs2)))
        ('C.FSDSP
         `(RV32D FSD (rs2 . ,rs2) (rs1 . 2) (imm . ,uimm)))
        ;; C.SQSP (128)
        ('C.SWSP
         `(RV32I SW (rs2 . ,rs2) (rs1 . 2) (imm . ,uimm)))
        ;; C.FSWSP (32)
        ('C.SDSP
         `(RV64I SD (rs1 . 2) (rs2 . ,rs2) (imm . ,uimm)))
        (_ i)))))

(defun rv-instruction-execute (st instruction xlen)
  "Execute an INSTRUCTION (given as an S-expression), altering and
returning the overall state ST, with XLEN."
  (let* ((instr (if (eq (car instruction) 'RVC)
                    (progn
                      ;; (message "Decompressing %s" instruction)
                      (rv-decompress instruction))
                  instruction))

         (params (cddr instr))
         (rd (cdr (assoc 'rd params)))
         (rs1 (cdr (assoc 'rs1 params)))
         (rs2 (cdr (assoc 'rs2 params)))
         (imm (cdr (assoc 'imm params)))
         (shamt (cdr (assoc 'shamt params)))
         (rm (cdr (assoc 'rm params)))

         (pc (cdr (assq 'pc st)))
         (mem (cdr (assq 'mem st)))
         (r (cdr (assq 'r st)))
         (f (cdr (assq 'f st)))

         (next-pc (+ pc (if (eq (car instruction) 'RVC) 2 4)))
         )
    ;; (message "pc=%d (%x) d=%s r=%s" pc pc instr
    ;;          (seq-map (lambda (x) (format "%x" x)) r))
    (pcase (cadr instr)
      ;; RV32I
      ('LUI
       (rv-xw st rd (rv-sext imm 32 xlen)))
      ('AUIPC
       (rv-xw st rd (rv-from-int (+ (rv-to-int imm 32) pc) xlen)))
      ('JAL
       (rv-xw st rd next-pc)
       (setq next-pc (+ pc (rv-to-int imm 21))))
      ('JALR
       (rv-xw st rd next-pc)
       (setq next-pc (ash (ash (+ (rv-to-int (rv-xr st rs1) xlen)
                                  (rv-to-int imm 12))
                               (- 1))
                          1)))
      ('BEQ
       (when (= (rv-to-int (rv-xr st rs1) xlen)
                (rv-to-int (rv-xr st rs2) xlen))
         (setq next-pc (+ pc (rv-to-int imm 13)))))
      ('BNE
       (unless (= (rv-to-int (rv-xr st rs1) xlen)
                  (rv-to-int (rv-xr st rs2) xlen))
         (setq next-pc (+ pc (rv-to-int imm 13)))))
      ('BLT
       (when (< (rv-to-int (rv-xr st rs1) xlen)
                (rv-to-int (rv-xr st rs2) xlen))
         (setq next-pc (+ pc (rv-to-int imm 13)))))
      ('BGE
       (when (>= (rv-to-int (rv-xr st rs1) xlen)
                 (rv-to-int (rv-xr st rs2) xlen))
         (setq next-pc (+ pc (rv-to-int imm 13)))))
      ('BLTU
       (when (< (rv-xr st rs1) (rv-xr st rs2))
         (setq next-pc (+ pc (rv-to-int imm 13)))))
      ('BGEU
       (when (>= (rv-xr st rs1) (rv-xr st rs2))
         (setq next-pc (+ pc (rv-to-int imm 13)))))
      ('LB
       (rv-xw st rd
              (rv-sext
               (rv-read-num st
                            (+ (rv-to-int (rv-xr st rs1) xlen)
                               (rv-to-int imm 12))
                            1)
               8
               32)))
      ('LH
       (rv-xw st rd
              (rv-sext
               (rv-read-num st
                            (+ (rv-to-int (rv-xr st rs1) xlen)
                               (rv-to-int imm 12))
                            2)
               16
               32)))
      ('LW
       (rv-xw st rd
              (rv-sext
               (rv-read-num st
                            (+ (rv-to-int (rv-xr st rs1) xlen)
                               (rv-to-int imm 12))
                            4)
               32
               xlen)))
      ('LBU
       (rv-xw st rd
              (rv-read-num st
                           (+ (rv-to-int (rv-xr st rs1) xlen)
                              (rv-to-int imm 12))
                           1)))
      ('LHU
       (rv-xw st rd
              (rv-read-num st
                           (+ (rv-to-int (rv-xr st rs1) xlen)
                              (rv-to-int imm 12))
                           2)))
      ('SB
       (unless (rv-write-num st
                             (rv-xr st rs2)
                             (+ (rv-to-int (rv-xr st rs1) xlen)
                                (rv-to-int imm 12))
                             1)
         (setq next-pc nil)))
      ('SH
       (unless (rv-write-num st
                             (rv-xr st rs2)
                             (+ (rv-to-int (rv-xr st rs1) xlen)
                                (rv-to-int imm 12))
                             2)
         (setq next-pc nil)))
      ('SW
       (unless (rv-write-num st
                             (rv-xr st rs2)
                             (+ (rv-to-int (rv-xr st rs1) xlen)
                                (rv-to-int imm 12))
                             4)
         (setq next-pc nil)))
      ('ADDI
       (rv-xw st rd (rv-from-int (+ (rv-to-int (rv-xr st rs1) xlen)
                                   (rv-to-int imm 12))
                                xlen)))
      ('SLTI
       (rv-xw st rd (if (< (rv-to-int (rv-xr st rs1) xlen)
                          (rv-to-int imm 12))
                       1
                     0)))
      ('SLTIU
       (rv-xw st rd (if (< (rv-xr st rs1)
                          imm)
                       1
                     0)))
      ('XORI
       (rv-xw st rd (logxor (rv-xr st rs1) (rv-sext imm 12 xlen))))
      ('ORI
       (rv-xw st rd (logior (rv-xr st rs1) (rv-sext imm 12 xlen))))
      ('ANDI
       (rv-xw st rd (logand (rv-xr st rs1) (rv-sext imm 12 xlen))))
      ('SLLI
       (rv-xw st rd (ash (rv-xr st rs1) shamt)))
      ('SRLI
       (rv-xw st rd (ash (rv-xr st rs1) (- shamt))))
      ('SRAI
       (rv-xw st rd
              (rv-sext (ash (rv-xr st rs1) (- shamt))
                       (- xlen shamt)
                       xlen)))
      ('ADD
       (rv-xw st rd
              (rv-from-int
               (+ (rv-to-int (rv-xr st rs1) xlen)
                  (rv-to-int (rv-xr st rs2) xlen))
               xlen)))
      ('SUB
       (rv-xw st rd
              (rv-from-int
               (- (rv-to-int (rv-xr st rs1) xlen)
                  (rv-to-int (rv-xr st rs2) xlen))
               xlen)))
      ('SLL
       (rv-xw st rd (logand (ash (rv-xr st rs1) (rv-xr st rs2))
                           (- (expt 2 xlen) 1))))
      ('SLT
       (rv-xw st rd (if (< (rv-to-int (rv-xr st rs1) xlen)
                          (rv-to-int (rv-xr st rs2) xlen))
                       1
                     0)))
      ('SLTU
       (rv-xw st rd (if (< (rv-xr st rs1) (rv-xr st rs2)) 1 0)))
      ('XOR
       (rv-xw st rd (logxor (rv-xr st rs1) (rv-xr st rs2))))
      ('SRL
       (rv-xw st rd (ash (rv-xr st rs1) (- (rv-xr st rs2)))))
      ('SRA
       (rv-xw st rd
              (rv-sext (ash (rv-xr st rs1) (- (rv-xr st rs2)))
                       (- xlen (rv-xr st rs2))
                       xlen)))
      ('OR
       (rv-xw st rd (logior (rv-xr st rs1) (rv-xr st rs2))))
      ('AND
       (rv-xw st rd (logand (rv-xr st rs1) (rv-xr st rs2))))
      ('FENCE
       nil)
      ('ECALL
       (pcase (rv-xr st 17)
         (98                      ; futex
          (let ((uaddr (rv-xr st 10))
                (futex-op (rv-xr st 11))
                (val (rv-xr st 12))
                (timeout (rv-xr st 13))
                (uaddr2 (rv-xr st 14))
                (val3 (rv-xr st 15)))
            (message "futex")
            (cond
             ((= (logand #b1111111 futex-op) 0) ; FUTEX_WAIT
              (let ((futex-word-stored (rv-read-num st uaddr 4)))
                (rv-xw st 10 0)))
             ((= (logand #b1111111 futex-op) 1) ; FUTEX_WAKE
              (let ((futex-word-stored (rv-read-num st uaddr 4)))
                (rv-xw st 10 0)))
             (t (setq next-pc nil)))))
         (66                      ; writev
          (let ((fd (rv-xr st 10))
                (iov (rv-xr st 11))
                (iovcnt (rv-xr st 12))
                (n 0)
                (strings nil)
                (nbytes 0))
            (while (< n iovcnt)
              (let* ((cur-iov-ptr (+ iov (* n 8)))
                     (iov-base (rv-read-num st cur-iov-ptr 8))
                     (iov-len (rv-read-num st (+ cur-iov-ptr 8) 4)))
                (push
                 (list iov n iov-base iov-len
                       (rv-read-string st iov-base iov-len))
                 strings)
                (setq nbytes (+ nbytes iov-len)))
              (setq n (+ n 1)))
            (message "writev %d: %s" fd (reverse strings))
            (rv-xw st 10 nbytes)))
         (222                     ; mmap
          (let* ((addr (rv-xr st 10))
                 (length (rv-xr st 11))
                 (prot (rv-xr st 12))
                 (flags (rv-xr st 13))
                 (fd (rv-xr st 14))
                 (offset (rv-xr st 15))
                 (target-addr (if (= addr 0)
                                  (rv-map-find-free st length)
                                addr)))
            (message "mmap: addr %x len %d" target-addr length)
            (if (= flags #x22)    ; private, anonymous
                (progn
                  (push (cons target-addr (make-vector length 0)) mem)
                  (rv-xw st 10 target-addr))
              (message "Unsupported mmap flags")
              (setq next-pc nil))))
         (135                     ; rt_sigprocmask
          (let ((how (rv-xr st 10))
                (set (rv-xr st 11))
                (oldset (rv-xr st 12))
                (sigsetsize (rv-xr st 13)))
            ;; A no-op, signals shouldn't matter for now.
            (rv-xw st 10 0)))
         (178                     ; gettid
          (message "gettid")
          (rv-xw st 10 42))
         (172                     ; getpid
          (message "getpid")
          (rv-xw st 10 42))
         (173                     ; getppid
          (message "getppid")
          (rv-xw st 10 41))
         (174                     ; getuid
          (message "getuid")
          (rv-xw st 10 42))
         (175                     ; geteuid
          (message "geteuid")
          (rv-xw st 10 42))
         (176                     ; getgid
          (message "getgid")
          (rv-xw st 10 42))
         (177                     ; getegid
          (message "getegid")
          (rv-xw st 10 42))
         (155                   ; getpgid
          (let ((pid (rv-xr st 10)))
            (message "getpgid (%d)" pid)
            (rv-xw st 10 42)))
         (131                     ; tgkill
          (let ((tgid (rv-xr st 10))
                (tid (rv-xr st 11))
                (sig (rv-xr st 12)))
            (message "tgkill (%d, %d, %d)" tgid tid sig)
            (rv-xw st 10 0)))
         (134                     ; rt_sigaction
          (let ((signum (rv-xr st 10))
                (act (rv-xr st 11))
                (oldact (rv-xr st 12)))
            (message "rt_sigaction (%d, %x, %x)" signum act oldact)
            (rv-xw st 10 0)))
         (94                      ; exit_group
          (let ((status (rv-xr st 10)))
            (message "exit_group %d" status)
            (setq next-pc nil)))
         (214                     ; brk
          (let ((addr (rv-xr st 10)))
            (message "brk %d" addr)
            (rv-xw st 10 0)))
         (96                      ; set_tid_address
          (let ((tidptr (rv-xr st 10)))
            (message "set_tid_address %d" tidptr)
            (rv-xw st 10 0)))
         (99                      ; set_robust_list
          (let ((head (rv-xr st 10))
                (len (rv-xr st 11)))
            (message "set_robust_list %d %d" head len)
            (rv-xw st 10 (rv-from-int -1 64))))
         (261                     ; prlimit64
          (let ((pid (rv-xr st 10))
                (resource (rv-xr st 11))
                (new-limit (rv-xr st 12))
                (old-limit (rv-xr st 13)))
            (message "prlimit64 (%d, %d, %d, %d)"
                     pid resource new-limit old-limit)
            (cond
             ((and (= resource 3) (not (= old-limit 0)))
              ;; RLIMIT_STACK, inquiring
              (rv-write-num st #x1000 old-limit 8) ; soft limit
              (rv-write-num st #x1000 (+ old-limit 8) 8) ; hard limit
              (rv-xw st 10 0))
             (t (setq next-pc nil)))))
         (78                      ; readlinkat
          (let ((dirfd (rv-xr st 10))
                (pathname (rv-xr st 11))
                (buf (rv-xr st 12))
                (bufsiz (rv-xr st 13))
                (path-str "/usr/bin/a.out"))
            (message "readlinkat: %s" (rv-read-string st pathname))
            (rv-write-string st path-str buf)
            (rv-xw st 10 (length path-str))))
         (79                      ; fstatat
          (let ((dirfd (rv-xr st 10))
                (pathname (rv-xr st 11))
                (statbuf (rv-xr st 12))
                (flags (rv-xr st 13)))
            (message "fstatat (%d, %x, %x, %x): %s"
                     dirfd pathname statbuf flags
                     (rv-read-string st pathname))
            (rv-write-num st 0 (+ statbuf 0) 8) ; st_dev
            (rv-write-num st 0 (+ statbuf 8) 8) ; st_ino
            (rv-write-num st 0 (+ statbuf 16) 4) ; st_mode
            (rv-write-num st 0 (+ statbuf 20) 4) ; st_nlink
            (rv-write-num st 42 (+ statbuf 24) 4) ; st_uid
            (rv-write-num st 42 (+ statbuf 28) 4) ; st_gid
            (rv-write-num st 0 (+ statbuf 32) 16) ; st_rdev
            (rv-write-num st 0 (+ statbuf 48) 8) ; st_size
            (rv-write-num st 0 (+ statbuf 56) 8) ; st_blksize
            (rv-write-num st 0 (+ statbuf 64) 8) ; st_blocks
            ;; st_atim
            ;; st_mtim
            ;; st_ctim
            (rv-xw st 10 0)))
         (278                      ; getrandom
          (let ((buf (rv-xr st 10))
                (buflen (rv-xr st 11))
                (flags (rv-xr st 12)))
            (message "getrandom (%x, %d, %x)" buf buflen flags)
            (rv-write-string st (seq-take "random bytes" buflen) buf)
            (rv-xw st 10 buflen)))
         (226                      ; mprotect
          (let ((addr (rv-xr st 10))
                (len (rv-xr st 11))
                (prot (rv-xr st 12)))
            (message "mprotect (%x, %d, %d)" addr len prot)
            (rv-xw st 10 0)))
         (64                      ; write
          (let ((fd (rv-xr st 10))
                (buf (rv-xr st 11))
                (count (rv-xr st 12)))
            (message "write (%x, %x, %d): %s" fd buf count
                     (rv-read-string st buf count))
            (rv-xw st 10 count)))
         (29                    ; ioctl
          (let ((fd (rv-xr st 10))
                (request (rv-xr st 11))
                (arg1 (rv-xr st 12)))
            (message "ioctl (%d, %x)" fd request)
            (pcase request
              (#x540F           ; TIOCGPGRP
               (rv-write-num st 42 arg1 4)))
            (rv-xw st 10 0)))
         (154                    ; setpgid
          (let ((pid (rv-xr st 10))
                (pgid (rv-xr st 11)))
            (message "setpgid (%d, %d)" pid pgid)
            (rv-xw st 10 0)))
         (56                    ; openat
          (let ((dirfd (rv-xr st 10))
                (pathname (rv-xr st 11))
                (flags (rv-xr st 12)))
            (message "openat (%x, %x, %d): %s"
                     dirfd pathname flags
                     (rv-read-string st pathname))
            ;; TODO: add a file entry and so on
            (rv-xw st 10 3)))
         (25                    ; fcntl
          (let ((fd (rv-xr st 10))
                (cmd (rv-xr st 11))
                (arg1 (rv-xr st 12)))
            (message "fcntl (%d, %d, %d)"
                     fd cmd arg1)
            (pcase cmd
              (0 (rv-xw st 10 arg1)) ; F_DUPFD
              (1030 (rv-xw st 10 arg1))  ; F_DUPFD_CLOEXEC
              (2 (rv-xw st 10 0))    ; F_SETFD
              (_ (progn
                   (message "Unknown fcntl cmd")
                   (setq next-pc nil))))))
         (57                    ; close
          (let ((fd (rv-xr st 10)))
            (message "close (%d)" fd)
            (rv-xw st 10 0)))
         (129                   ; kill
          (let ((pid (rv-xr st 10))
                (sig (rv-xr st 11)))
            (message "kill (%d, %d)" pid sig)
            (rv-xw st 10 0)))
         (63                    ; read
          (let ((fd (rv-xr st 10))
                (buf (rv-xr st 11))
                (count (rv-xr st 12)))
            (message "read (%d, %x, %d)" fd buf count)
            (cond
             ((= fd 0)          ; stdin
              ;; Populate the input buffer, if empty
              (when (string-empty-p (cdr (assq 'stdin-buffer st)))
                (setf (cdr (assq 'stdin-buffer st))
                      (read-from-minibuffer
                       (format "stdin (%d): " count))))

              (let* ((in (cdr (assq 'stdin-buffer st))))
                (rv-write-string st
                                 (seq-take in count)
                                 buf)
                (setf (cdr (assq 'stdin-buffer st))
                      (seq-drop in count))
                (rv-xw st 10 (min (length in) count))))
             (t (rv-xw st 10 (rv-from-int -1 xlen))))))
         (_
          (message "Unsupported ECALL")
          (setq next-pc nil))))
      ('EBREAK
       (message "ebreak")
       (setq next-pc nil))

      ;; RV64I
      ('LWU
       (rv-xw st rd
              (rv-read-num st
                           (+ (rv-to-int (rv-xr st rs1) xlen)
                              (rv-to-int imm 12))
                           4)))
      ('LD
       (rv-xw st rd
              (rv-read-num st
                           (+ (rv-to-int (rv-xr st rs1) xlen)
                              (rv-to-int imm 12))
                           8)))
      ('SD
       (unless (rv-write-num st
                             (rv-xr st rs2)
                             (+ (rv-to-int (rv-xr st rs1) xlen)
                                (rv-to-int imm 12))
                             8)
         (setq next-pc nil)))
      ;; SLLI, SRLI, and SRAI are implemented in the RV32I part
      ('ADDIW
       (rv-xw st rd (rv-from-int (+ (rv-to-int (rv-xr st rs1) xlen)
                                   (rv-to-int imm 12))
                                xlen)))
      ('SLLIW
       (rv-xw st rd
              (logand (ash (rv-xr st rs1) shamt)
                      (- (expt 2 32) 1))))
      ('SRLIW
       (rv-xw st rd
              (ash (rv-xr st rs1) (- shamt))))
      ('SRAIW
       (rv-xw st rd
              (rv-sext (ash (rv-xr st rs1) (- shamt))
                       (- 32 shamt)
                       32)))
      ('ADDW
       (rv-xw st rd
              (rv-sext
               (rv-from-int
                (+ (rv-to-int (rv-xr st rs1) 32)
                   (rv-to-int (rv-xr st rs2) 32))
                32)
               32
               64)))
      ('SUBW
       (rv-xw st rd
              (rv-sext
               (rv-from-int
                (- (rv-to-int (rv-xr st rs1) 32)
                   (rv-to-int (rv-xr st rs2) 32))
                32)
               32
               64)))
      ('SLLW
       (rv-xw st rd
              (logand (ash (logand (rv-xr st rs1) (- (expt 2 32) 1))
                           (logand (rv-xr st rs2) (- (expt 2 32) 1)))
                      (- (expt 2 32) 1))))
      ('SRLW
       (rv-xw st rd
              (logand (ash (logand (rv-xr st rs1) (- (expt 2 32) 1))
                           (- (logand (rv-xr st rs2) (- (expt 2 32) 1))))
                      (- (expt 2 32) 1))))
      ('SRAW
       (rv-xw st rd
              (rv-sext (ash (logand (rv-xr st rs1) (- (expt 2 32) 1))
                            (- (logand (rv-xr st rs2) (- (expt 2 32) 1))))
                       (- 32 (logand (rv-xr st rs2) (- (expt 2 32) 1)))
                       32)))

      ;; RV32A
      ('LR.W
       ;; TODO: reserved set
       (rv-xw st rd
              (rv-sext
               (rv-read-num st (rv-xr st rs1) 4)
               32
               xlen)))
      ('SC.W
       ;; TODO: check reserved set
       (let ((rs1-val (rv-xr st rs1))
             (rs2-val (rv-xr st rs2)))
         (rv-write-num st
                       rs2-val
                       rs1-val
                       4)
         (rv-xw st rd 0)))
      ('AMOSWAP.W
       (let* ((rs1-val (rv-xr st rs1))
              (rs1-referenced-val (rv-read-num st rs1-val 4))
              (rs2-val (rv-xr st rs2)))
         (rv-xw st rd rs1-referenced-val)
         (rv-write-num st
                       rs2-val
                       rs1-val
                       4)))

      ;; RV64A
      ('AMOSWAP.D
       (let* ((rs1-val (rv-xr st rs1))
              (rs1-referenced-val (rv-read-num st rs1-val 8))
              (rs2-val (rv-xr st rs2)))
         (rv-xw st rd rs1-referenced-val)
         (rv-write-num st
                       rs2-val
                       rs1-val
                       8)))
      ;; RV32M
      ('MUL
       (rv-xw st rd (rv-from-int (* (rv-to-int (rv-xr st rs1) xlen)
                                   (rv-to-int (rv-xr st rs2) xlen))
                                xlen)))
      ('DIVU
       (rv-xw st rd (floor (/ (rv-xr st rs1) (rv-xr st rs2)))))
      ('REMU
       (rv-xw st rd (mod (rv-xr st rs1) (rv-xr st rs2))))

      ;; RV64M
      ('MULW
       (rv-xw st rd (rv-from-int (* (rv-to-int (rv-xr st rs1) 32)
                                   (rv-to-int (rv-xr st rs2) 32))
                                32)))
      ('DIVUW
       (rv-xw st rd (floor (/ (logand (rv-xr st rs1) (- (expt 2 32) 1))
                             (logand (rv-xr st rs2) (- (expt 2 32) 1))))))
      ('REMUW
       (rv-xw st rd (mod (logand (rv-xr st rs1) (- (expt 2 32) 1))
                        (logand (rv-xr st rs2) (- (expt 2 32) 1)))))

      ;; RV32D
      ('FLD
       (rv-fw st rd
              (rv-read-num st
                           (+ (rv-to-int (rv-xr st rs1) xlen)
                              (rv-to-int imm 12))
                           8)))
      ('FSD
       (unless (rv-write-num st
                             (rv-fr st rs2)
                             (+ (rv-to-int (rv-xr st rs1) xlen)
                                (rv-to-int imm 12))
                             8)
         (setq next-pc nil)))
      ('FCVT.D.W
       (rv-fw st rd
              (rv-from-float (float (rv-to-int (rv-xr st rs1) 32))
                             64)))
      ('FCVT.D.L
       ;; TODO: rounding according to rm
       (rv-fw st rd
              (rv-from-float (float (rv-to-int (rv-xr st rs1) 64))
                             64)))
      ('FCVT.W.D
       ;; TODO: rounding according to rm
       (rv-xw st rd
              (rv-from-int (round (rv-to-float (rv-fr st rs1) 64))
                           32)))
      ('FCVT.L.D
       ;; TODO: rounding according to rm
       (rv-xw st rd
              (rv-from-int (round (rv-to-float (rv-fr st rs1) 64))
                           64)))
      ('FMUL.D
       (rv-fw st rd
              (rv-from-float (* (rv-to-float (rv-fr st rs1) 64)
                                (rv-to-float (rv-fr st rs2) 64))
                             64)))
      ('FADD.D
       (rv-fw st rd
              (rv-from-float (+ (rv-to-float (rv-fr st rs1) 64)
                                (rv-to-float (rv-fr st rs2) 64))
                             64)))
      ('FSUB.D
       (rv-fw st rd
              (rv-from-float (- (rv-to-float (rv-fr st rs1) 64)
                                (rv-to-float (rv-fr st rs2) 64))
                             64)))
      (_ (message "Unsupported instruction: %s" instr)
         (setq next-pc nil)))
    (when (and rd (not (rv-xr st rd)))
      (setq next-pc nil))

    (setf (cdr (assq 'instruction-count st))
          (1+ (cdr (assq 'instruction-count st)))

          (cdr (assq 'pc st))
          next-pc

          (cdr (assq 'mem st))
          mem)
    st))

(defun rv-instruction-execute-raw (state raw-instruction xlen)
  "Execute a raw (not decoded) instruction, presented as a number."
  (let ((instruction (rv-decode raw-instruction)))
    (if instruction
        (rv-instruction-execute state instruction xlen)
      (message "Unsupported instruction: %x" raw-instruction)
      (setf (cdr (assq 'pc state)) nil))))

(defun rv-step (state xlen)
  "Read the next instruction, execute it.."
  (let* ((i-byte (rv-read-byte state
                               (cdr (assq 'pc state))))
         (i-width (if (= (logand i-byte #b11) #b11) 4 2))
         (i (rv-read-num state
                         (cdr (assq 'pc state))
                         i-width)))
    (if (not i)
        (progn
          (message "No more instructions at pc=%d (%x)"
                   (cdr (assq 'pc state)) (cdr (assq 'pc state)))
          (assq-delete-all 'pc state))
      (rv-instruction-execute-raw state i xlen))))

;;;###autoload
(defun rv-elf-run (elf-filename)
  "Load a program from an ELF file, run it."
  (interactive "fELF executable: ")
  (let* ((xlen 64)
         (r (make-vector 32 0))
         (f (make-vector 32 0))
         (elf (rv-load-file elf-filename))
         (elf-32-bit (eq (rv-read-num elf 4 1) 1))
         (elf-big-endian (eq (rv-read-num elf 5 1) 2))
         (pc (rv-read-num elf #x18 (if elf-32-bit 4 8) elf-big-endian))
         (elf-phoff (rv-read-num elf (if elf-32-bit #x1C #x20)
                                 (if elf-32-bit 4 8) elf-big-endian))
         (elf-shoff (rv-read-num elf (if elf-32-bit #x20 #x28)
                                 (if elf-32-bit 4 8) elf-big-endian))
         (elf-phentsize (rv-read-num elf (if elf-32-bit #x2A #x36)
                                     2 elf-big-endian))
         (elf-phnum (rv-read-num elf (if elf-32-bit #x2C #x38)
                                 2 elf-big-endian))
         (elf-shentsize (rv-read-num elf (if elf-32-bit #x2E #x3A)
                                     2 elf-big-endian))
         (elf-shnum (rv-read-num elf (if elf-32-bit #x30 #x3C)
                                 2 elf-big-endian))
         (elf-shstrndx (rv-read-num elf (if elf-32-bit #x32 #x3E)
                                    2 elf-big-endian))

         (stack-lower #x574c0000)
         (stack-size #x10000)
         (stack-pointer (+ stack-lower stack-size))
         (mem (list (cons stack-lower (make-vector stack-size 0))))
         (st (list (cons 'mem mem)))
         (stack-push-num (lambda (val &optional size)
                           (setq size (or size 8))
                           (setq stack-pointer (- stack-pointer size))
                           (rv-write-num st val stack-pointer size)
                           stack-pointer))
         (stack-push-string (lambda (str)
                              (setq stack-pointer
                                    (- stack-pointer (length str) 1))
                              (rv-write-string st str stack-pointer)
                              stack-pointer)))
    (message "elf 32-bit=%S BE=%S EP=0x%X phoff=%d phentsize=%d phnum=%d"
             elf-32-bit elf-big-endian pc elf-phoff elf-phentsize elf-phnum)
    (let ((n 0))
      (while (< n elf-phnum)
        (let* ((ph-base (+ elf-phoff (* n elf-phentsize)))
               (p-type (rv-read-num elf ph-base 4 elf-big-endian))
               (p-flags (rv-read-num elf
                                     (+ ph-base (if elf-32-bit #x18 #x4))
                                     4
                                     elf-big-endian))
               (p-offset (rv-read-num elf
                                      (+ ph-base (if elf-32-bit #x4 #x8))
                                      (if elf-32-bit 4 8)
                                      elf-big-endian))
               (p-vaddr (rv-read-num elf
                                     (+ ph-base (if elf-32-bit #x8 #x10))
                                     (if elf-32-bit 4 8)
                                     elf-big-endian))
               (p-paddr (rv-read-num elf
                                     (+ ph-base (if elf-32-bit #x0C #x18))
                                     (if elf-32-bit 4 8)
                                     elf-big-endian))
               (p-filesz (rv-read-num elf
                                      (+ ph-base (if elf-32-bit #x10 #x20))
                                      (if elf-32-bit 4 8)
                                      elf-big-endian))
               (p-memsz (rv-read-num elf
                                     (+ ph-base (if elf-32-bit #x14 #x28))
                                     (if elf-32-bit 4 8)
                                     elf-big-endian))
               (p-align (rv-read-num elf
                                     (+ ph-base (if elf-32-bit #x1C #x30))
                                     (if elf-32-bit 4 8)
                                     elf-big-endian))
               )
          (message "PH type=0x%X flags=0x%X offset=0x%X vaddr=0x%X paddr=0x%X filesz=0x%X memsz=0x%X align=0x%X"
                   p-type p-flags p-offset p-vaddr p-paddr p-filesz p-memsz p-align)
          (when (= p-type 1)
            ;; PT_LOAD: add memory maps
            (push (cons p-vaddr
                        (seq-concatenate
                         'vector
                         (seq-subseq elf p-offset (+ p-offset p-filesz))
                         (if (< p-filesz p-memsz)
                             (make-vector (- p-memsz p-filesz) 0)
                           (vector))))
                  mem)))
        (setq n (+ n 1))))
    (let ((n 0))
      (while (< n elf-shnum)
        (let* ((sh-base (+ elf-shoff (* n elf-shentsize)))
               (sh-name (rv-read-num elf sh-base 4 elf-big-endian))
               (sh-type (rv-read-num elf (+ sh-base 4) 4 elf-big-endian))
               (sh-flags (rv-read-num elf
                                      (+ sh-base 8)
                                      (if elf-32-bit 4 8)
                                      elf-big-endian))
               (sh-addr (rv-read-num elf
                                     (+ sh-base (if elf-32-bit #x0C #x10))
                                     (if elf-32-bit 4 8)
                                     elf-big-endian))
               (sh-offset (rv-read-num elf
                                       (+ sh-base (if elf-32-bit #x10 #x18))
                                       (if elf-32-bit 4 8)
                                       elf-big-endian))
               (sh-size (rv-read-num elf
                                     (+ sh-base (if elf-32-bit #x14 #x20))
                                     (if elf-32-bit 4 8)
                                     elf-big-endian))
               )
          (message "SH type=0x%X flags=0x%X addr=0x%X offset=0x%X size=0x%X"
                   sh-type sh-flags sh-addr sh-offset sh-size)
          )
        (setq n (+ n 1))))

    ;; Add a separate memory map for stack
    ;; (push (cons stack-lower (make-vector stack-size 0)) mem)

    (let* ((fn-str-ptr (funcall stack-push-string elf-filename))
           (lang-str-ptr (funcall stack-push-string "LANG=C.UTF-8"))
           (home-str-ptr (funcall stack-push-string "HOME=/home/user"))
           (pwd-str-ptr (funcall stack-push-string "PWD=/home/user"))
           (term-str-ptr (funcall stack-push-string "TERM=dumb"))
           (user-str-ptr (funcall stack-push-string "USER=user"))
           (random-str-ptr (funcall stack-push-string "non-random bytes")))
      ;; End of auxillary vector, NULL
      (funcall stack-push-num 0)
      ;; AT_RANDOM
      (funcall stack-push-num random-str-ptr)
      (funcall stack-push-num 25)
      ;; AT_EGID
      (funcall stack-push-num 42)
      (funcall stack-push-num 14)
      ;; AT_GID
      (funcall stack-push-num 42)
      (funcall stack-push-num 13)
      ;; AT_EUID
      (funcall stack-push-num 1)
      (funcall stack-push-num 12)
      ;; AT_UID
      (funcall stack-push-num 1)
      (funcall stack-push-num 11)
      ;; AT_CLKTCK
      (funcall stack-push-num 100)
      (funcall stack-push-num 17)
      ;; AT_PAGESZ
      (funcall stack-push-num #x1000)
      (funcall stack-push-num 6)
      ;; AT_ENTRY
      (funcall stack-push-num pc)
      (funcall stack-push-num 9)
      ;; AT_EXECFN
      (funcall stack-push-num fn-str-ptr)
      (funcall stack-push-num 31)
      ;; NULL between the start of auxilary vector and the end of
      ;; environment variables.
      (funcall stack-push-num 0)
      ;; Environment variables
      (funcall stack-push-num lang-str-ptr)
      (funcall stack-push-num home-str-ptr)
      (funcall stack-push-num pwd-str-ptr)
      (funcall stack-push-num term-str-ptr)
      (funcall stack-push-num user-str-ptr)
      ;; NULL between argv and environment variables
      (funcall stack-push-num 0)
      ;; argv
      (funcall stack-push-num fn-str-ptr)
      ;; argc
      (funcall stack-push-num 1))

    (setq st
          (list (cons 'pc pc)
                (cons 'mem mem)
                (cons 'r r)
                (cons 'f f)
                (cons 'instruction-count 0)
                (cons 'stdin-buffer "")))

    ;; Set the x2 (sp) register to the resulting stack pointer
    (rv-xw st 2 stack-pointer)

    (while (and (cdr (assq 'pc st)) (> (cdr (assq 'pc st)) 0))
      (setq st (rv-step st xlen)))
    (message "pc=%s cnt=%d r=%s" (cdr (assq 'pc st))
             (cdr (assq 'instruction-count st))
             (seq-map (lambda (x) (format "%x" x)) r))))

;; (rv-elf-run "a.out")
;; (rv-elf-run "../dash/src/dash")

;;; rv.el ends here
