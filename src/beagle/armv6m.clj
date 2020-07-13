(ns beagle.armv6m
    (:refer-clojure :only [* + - < << <= = >> >>> aget and aset bit-and bit-not bit-or bit-xor byte-array cond cons dec defmacro defn first if-not inc next not object-array or pos? when when-not zero?])
)

(defmacro § [& _])
(defmacro ß [& _])

(defmacro about [& s] (cons 'do s))

(defmacro assert [_])
(defmacro throw! [_])

(about #_"armv6m"

    (def mask'EVAL_0 0xf000)
    (def mask'EVAL_1 0xf800)
    (def mask'EVAL_2 0xfe00)
    (def mask'EVAL_3 0xff00)
    (def mask'EVAL_4 0xff80)
    (def mask'EVAL_5 0xffc0)
    (def mask'EVAL_6 0xffe0)
    (def mask'EVAL_7 0xfff0)
    (def mask'EVAL_8 0xffff)

    (def code'ADCS   0x4140) (def mask'ADCS   0xffc0) #_"ADCS <Rdn>,<Rm>"
    (def code'ADDS   0x1c00) (def mask'ADDS   0xfe00) #_"ADDS <Rd>,<Rn>,#<imm3>"
    (def code'ADDS_1 0x3000) (def mask'ADDS_1 0xf800) #_"ADDS <Rdn>,#<imm8>"
    (def code'ADDS_2 0x1800) (def mask'ADDS_2 0xfe00) #_"ADDS <Rd>,<Rn>,<Rm>"
    (def code'ADD    0x4400) (def mask'ADD    0xff00) #_"ADD <Rdn>,<Rm>"
    (def code'ADD_1  0xa800) (def mask'ADD_1  0xf800) #_"ADD <Rd>,SP,#<imm8>"
    (def code'ADD_2  0xb000) (def mask'ADD_2  0xff80) #_"ADD SP,SP,#<imm7>"
    (def code'ADR    0xa000) (def mask'ADR    0xf800) #_"ADR <Rd>,<label>"
    (def code'ANDS   0x4000) (def mask'ANDS   0xffc0) #_"ANDS <Rdn>,<Rm>"
    (def code'ASRS   0x1000) (def mask'ASRS   0xf800) #_"ASRS <Rd>,<Rm>,#<imm5>"
    (def code'ASRS_1 0x4100) (def mask'ASRS_1 0xffc0) #_"ASRS <Rdn>,<Rm>"
    (def code'BCC    0xd000) (def mask'BCC    0xf000) #_"BCC <label>"
    (def code'B      0xe000) (def mask'B      0xf800) #_"B <label>"
    (def code'BICS   0x4380) (def mask'BICS   0xffc0) #_"BICS <Rdn>,<Rm>"
    (def code'BKPT   0xbe00) (def mask'BKPT   0xff00) #_"BKPT #<imm8>"
    (def code'BL     0xf000) (def mask'BL     0xf800) #_"BL <label>"
    (def code'BLX    0x4780) (def mask'BLX    0xff80) #_"BLX <Rm>"
    (def code'BX     0x4700) (def mask'BX     0xff80) #_"BX <Rm>"
    (def code'CMN    0x42c0) (def mask'CMN    0xffc0) #_"CMN <Rn>,<Rm>"
    (def code'CMP    0x2800) (def mask'CMP    0xf800) #_"CMP <Rn>,#<imm8>"
    (def code'CMP_1  0x4280) (def mask'CMP_1  0xffc0) #_"CMP <Rn>,<Rm> <Rn> and <Rm> both from R0-R7"
    (def code'CMP_2  0x4500) (def mask'CMP_2  0xff00) #_"CMP <Rn>,<Rm> <Rn> and <Rm> not both from R0-R7"
    (def code'CPS    0xb660) (def mask'CPS    0xffe0) #_"CPS<effect> i"
    (def code'DMB    0xf3b0) (def mask'DMB    0xfff0) #_"DMB #<option>"
    (def code'DSB    0xf3b0) (def mask'DSB    0xfff0) #_"DSB #<option>"
    (def code'EORS   0x4040) (def mask'EORS   0xffc0) #_"EORS <Rdn>,<Rm>"
    (def code'ISB    0xf3b0) (def mask'ISB    0xfff0) #_"ISB #<option>"
    (def code'LDM    0xc800) (def mask'LDM    0xf800) #_"LDM <Rn>!,<registers> <Rn> not included in <registers>"
    (def code'LDM_1  0xc800) (def mask'LDM_1  0xf800) #_"LDM <Rn>,<registers> <Rn> included in <registers>"
    (def code'LDR    0x6800) (def mask'LDR    0xf800) #_"LDR <Rt>,[<Rn>{,#<imm5>}]"
    (def code'LDR_1  0x9800) (def mask'LDR_1  0xf800) #_"LDR <Rt>,[SP{,#<imm8>}]"
    (def code'LDR_2  0x4800) (def mask'LDR_2  0xf800) #_"LDR <Rt>,<label>"
    (def code'LDR_3  0x5800) (def mask'LDR_3  0xfe00) #_"LDR <Rt>,[<Rn>,<Rm>]"
    (def code'LDRB   0x7800) (def mask'LDRB   0xf800) #_"LDRB <Rt>,[<Rn>{,#<imm5>}]"
    (def code'LDRB_1 0x5c00) (def mask'LDRB_1 0xfe00) #_"LDRB <Rt>,[<Rn>,<Rm>]"
    (def code'LDRH   0x8800) (def mask'LDRH   0xf800) #_"LDRH <Rt>,[<Rn>{,#<imm5>}]"
    (def code'LDRH_1 0x5a00) (def mask'LDRH_1 0xfe00) #_"LDRH <Rt>,[<Rn>,<Rm>]"
    (def code'LDRSB  0x5600) (def mask'LDRSB  0xfe00) #_"LDRSB <Rt>,[<Rn>,<Rm>]"
    (def code'LDRSH  0x5e00) (def mask'LDRSH  0xfe00) #_"LDRSH <Rt>,[<Rn>,<Rm>]"
    (def code'LSLS   0x0000) (def mask'LSLS   0xf800) #_"LSLS <Rd>,<Rm>,#<imm5>"
    (def code'LSLS_1 0x4080) (def mask'LSLS_1 0xffc0) #_"LSLS <Rdn>,<Rm>"
    (def code'LSRS   0x0800) (def mask'LSRS   0xf800) #_"LSRS <Rd>,<Rm>,#<imm5>"
    (def code'LSRS_1 0x40c0) (def mask'LSRS_1 0xffc0) #_"LSRS <Rdn>,<Rm>"
    (def code'MOVS   0x2000) (def mask'MOVS   0xf800) #_"MOVS <Rd>,#<imm8>"
    (def code'MOV    0x4600) (def mask'MOV    0xff00) #_"MOV <Rd>,<Rm> Otherwise all versions of the Thumb instruction set."
    (def code'MOVS_1 0x0000) (def mask'MOVS_1 0xffc0) #_"MOVS <Rd>,<Rm>"
    (def code'MRS    0xf3e0) (def mask'MRS    0xffe0) #_"MRS <Rd>,<spec_reg>"
    (def code'MSR    0xf380) (def mask'MSR    0xffe0) #_"MSR <spec_reg>,<Rn>"
    (def code'MULS   0x4340) (def mask'MULS   0xffc0) #_"MULS <Rdm>,<Rn>,<Rdm>"
    (def code'MVNS   0x43c0) (def mask'MVNS   0xffc0) #_"MVNS <Rd>,<Rm>"
    (def code'NOP    0xbf00) (def mask'NOP    0xffff) #_"NOP"
    (def code'ORRS   0x4300) (def mask'ORRS   0xffc0) #_"ORRS <Rdn>,<Rm>"
    (def code'POP    0xbc00) (def mask'POP    0xfe00) #_"POP <registers>"
    (def code'PUSH   0xb400) (def mask'PUSH   0xfe00) #_"PUSH <registers>"
    (def code'REV    0xba00) (def mask'REV    0xffc0) #_"REV <Rd>,<Rm>"
    (def code'REV16  0xba40) (def mask'REV16  0xffc0) #_"REV16 <Rd>,<Rm>"
    (def code'REVSH  0xbac0) (def mask'REVSH  0xffc0) #_"REVSH <Rd>,<Rm>"
    (def code'RORS   0x41c0) (def mask'RORS   0xffc0) #_"RORS <Rdn>,<Rm>"
    (def code'RSBS   0x4240) (def mask'RSBS   0xffc0) #_"RSBS <Rd>,<Rn>,#0"
    (def code'SBCS   0x4180) (def mask'SBCS   0xffc0) #_"SBCS <Rdn>,<Rm>"
    (def code'SEV    0xbf40) (def mask'SEV    0xffff) #_"SEV"
    (def code'STM    0xc000) (def mask'STM    0xf800) #_"STM <Rn>!,<registers>"
    (def code'STR    0x6000) (def mask'STR    0xf800) #_"STR <Rt>,[<Rn>{,#<imm5>}]"
    (def code'STR_1  0x9000) (def mask'STR_1  0xf800) #_"STR <Rt>,[SP,#<imm8>]"
    (def code'STR_2  0x5000) (def mask'STR_2  0xfe00) #_"STR <Rt>,[<Rn>,<Rm>]"
    (def code'STRB   0x7000) (def mask'STRB   0xf800) #_"STRB <Rt>,[<Rn>,#<imm5>]"
    (def code'STRB_1 0x5400) (def mask'STRB_1 0xfe00) #_"STRB <Rt>,[<Rn>,<Rm>]"
    (def code'STRH   0x8000) (def mask'STRH   0xf800) #_"STRH <Rt>,[<Rn>{,#<imm5>}]"
    (def code'STRH_1 0x5200) (def mask'STRH_1 0xfe00) #_"STRH <Rt>,[<Rn>,<Rm>]"
    (def code'SUBS   0x1e00) (def mask'SUBS   0xfe00) #_"SUBS <Rd>,<Rn>,#<imm3>"
    (def code'SUBS_1 0x3800) (def mask'SUBS_1 0xf800) #_"SUBS <Rdn>,#<imm8>"
    (def code'SUBS_2 0x1a00) (def mask'SUBS_2 0xfe00) #_"SUBS <Rd>,<Rn>,<Rm>"
    (def code'SUB    0xb080) (def mask'SUB    0xff80) #_"SUB SP,SP,#<imm7>"
    (def code'SVC    0xdf00) (def mask'SVC    0xff00) #_"SVC #<imm8>"
    (def code'SXTB   0xb240) (def mask'SXTB   0xffc0) #_"SXTB <Rd>,<Rm>"
    (def code'SXTH   0xb200) (def mask'SXTH   0xffc0) #_"SXTH <Rd>,<Rm>"
    (def code'TST    0x4200) (def mask'TST    0xffc0) #_"TST <Rn>,<Rm>"
    (def code'UDF    0xde00) (def mask'UDF    0xff00) #_"UDF #<imm8>"
    (def code'UDF_W  0xf7f0) (def mask'UDF_W  0xfff0) #_"UDF_W #<imm16>"
    (def code'UXTB   0xb2c0) (def mask'UXTB   0xffc0) #_"UXTB <Rd>,<Rm>"
    (def code'UXTH   0xb280) (def mask'UXTH   0xffc0) #_"UXTH <Rd>,<Rm>"
    (def code'WFE    0xbf20) (def mask'WFE    0xffff) #_"WFE"
    (def code'WFI    0xbf30) (def mask'WFI    0xffff) #_"WFI"
    (def code'YIELD  0xbf10) (def mask'YIELD  0xffff) #_"YIELD"
)

(about #_"ram"

    (defn #_"ram" ram'new [#_"u32" base, #_"u32" size] (cons base (byte-array size)))

    (defn #_"u32" ram'base [#_"ram" this] (first this))
    (defn #_"[u8]" ram'mem [#_"ram" this] (next this))

    (defn #_"void" ram''write8 [#_"ram" this, #_"u32" addr, #_"u8" data]
        (aset (ram'mem this) (- addr (ram'base this)) data)
        nil
    )

    (defn #_"void" ram''write16 [#_"ram" this, #_"u32" addr, #_"u32" data]
        (ram''write8 this, (+ addr 0), (>>> data 0))
        (ram''write8 this, (+ addr 1), (>>> data 8))
        nil
    )

    (defn #_"void" ram''write32 [#_"ram" this, #_"u32" addr, #_"u32" data]
        (ram''write8 this, (+ addr 0), (>>> data  0))
        (ram''write8 this, (+ addr 1), (>>> data  8))
        (ram''write8 this, (+ addr 2), (>>> data 16))
        (ram''write8 this, (+ addr 3), (>>> data 24))
        nil
    )

    (defn #_"u8" ram''read8 [#_"ram" this, #_"u32" addr]
        (aget (ram'mem this) (- addr (ram'base this)))
    )

    (defn #_"u16" ram''read16 [#_"ram" this, #_"u32" addr]
        (§ cast #_"u16"
            (bit-or
                (<< (§ cast #_"u32" (ram''read8 this, (+ addr 0))) 0)
                (<< (§ cast #_"u32" (ram''read8 this, (+ addr 1))) 8)
            )
        )
    )

    (defn #_"u32" ram''read32 [#_"ram" this, #_"u32" addr]
        (§ cast #_"u32"
            (bit-or
                (<< (§ cast #_"u32" (ram''read8 this, (+ addr 0)))  0)
                (<< (§ cast #_"u32" (ram''read8 this, (+ addr 1)))  8)
                (<< (§ cast #_"u32" (ram''read8 this, (+ addr 2))) 16)
                (<< (§ cast #_"u32" (ram''read8 this, (+ addr 3))) 24)
            )
        )
    )
)

(about #_"cpu"

    (def shift'N 31)
    (def shift'Z 30)
    (def shift'C 29)
    (def shift'V 28)

    (def flag'N (<< 1 shift'N))
    (def flag'Z (<< 1 shift'Z))
    (def flag'C (<< 1 shift'C))
    (def flag'V (<< 1 shift'V))

    (def flags'all (bit-or flag'N flag'Z flag'C flag'V))
    (def flags'NZC (bit-or flag'N flag'Z flag'C))

    (def PRIMASK_PM (<< 1 0))

    (def CONTROL_NPRIV (<< 1 0))
    (def CONTROL_SPSEL (<< 1 1))
    (def CONTROL_MASK  (bit-or CONTROL_NPRIV CONTROL_SPSEL))

    (def EXC_RETURN 0xffffffe0)

    (def i'sp         13) #_"u32"
    (def i'lr         14) #_"u32"
    (def i'pc         15) #_"u32"

    (def size'regfile 16)

    (def i'ram        16) #_"ram"

    (def i'psp        17) #_"u32"
    (def i'msp        18) #_"u32"
    (def i'apsr       19) #_"u32"
    (def i'ipsr       20) #_"u32"
    (def i'epsr       21) #_"u32"

    (def i'primask    22) #_"u32"
    (def i'control    23) #_"u32"

    (def i'handler?   24) #_"bool"

    (def size'cpu     25)

    (defn #_"cpu" cpu'new [#_"ram" ram]
        (let [
            #_"cpu" this (object-array size'cpu)
        ]
            (aset this i'ram ram)

            (aset this i'sp          (cpu''read32 this,    (ram'base ram)))
            (aset this i'pc (bit-and (cpu''read32 this, (+ (ram'base ram) 4)) (bit-not 1)))

            (aset this i'msp (aget this i'sp))

            this
        )
    )

    (defn #_"void" cpu''write8  [#_"cpu" this, #_"u32" addr, #_"u8"  data] (ram''write8  (aget this i'ram),          addr,              data) nil)
    (defn #_"void" cpu''write16 [#_"cpu" this, #_"u32" addr, #_"u16" data] (ram''write16 (aget this i'ram), (bit-and addr (bit-not 1)), data) nil)
    (defn #_"void" cpu''write32 [#_"cpu" this, #_"u32" addr, #_"u32" data] (ram''write32 (aget this i'ram), (bit-and addr (bit-not 3)), data) nil)

    (defn #_"u8"  cpu''read8  [#_"cpu" this, #_"u32" addr] (ram''read8  (aget this i'ram),          addr))
    (defn #_"u16" cpu''read16 [#_"cpu" this, #_"u32" addr] (ram''read16 (aget this i'ram), (bit-and addr (bit-not 1))))
    (defn #_"u32" cpu''read32 [#_"cpu" this, #_"u32" addr] (ram''read32 (aget this i'ram), (bit-and addr (bit-not 3))))

    (defn #_"u16" armv6m''fetch [#_"armv6m" this, #_"u32" addr]
        (if (zero? (bit-and addr 0x2))
            (bit-and (>>> (cpu''read32 this, addr)  0) 0xffff)
            (bit-and (>>> (cpu''read32 this, addr) 16) 0xffff)
        )
    )

    (defn #_"void" armv6m''update_sp [#_"armv6m" this, #_"u32" addr]
        (aset this i'sp addr)

        (if (or (aget this i'handler?) (zero? (bit-and (aget this i'control) CONTROL_SPSEL)))
            (aset this i'msp addr)
            (aset this i'psp addr)
        )
        nil
    )

    (defn #_"void" armv6m''update_rd [#_"armv6m" this, #_"u32" rd, #_"u32" word]
        (if (= rd i'sp)
            (armv6m''update_sp this, word)
            (do
                (assert (not (= rd i'pc)))
                (aset this rd word)
            )
        )
        nil
    )

    (defn #_"void" armv6m''update_nz [#_"armv6m" this, #_"u32" word]
        (if (zero? word) #_"Zero"
            (aset this i'apsr (bit-or  (aget this i'apsr)          flag'Z))
            (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'Z)))
        )

        (if-not (zero? (bit-and word 0x80000000)) #_"Negative"
            (aset this i'apsr (bit-or  (aget this i'apsr)          flag'N))
            (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'N)))
        )
        nil
    )

    (defn #_"armv6m" armv6m''update_pc [#_"armv6m" this, #_"u32" addr]
        (aset this i'pc addr)
        this
    )

    (defn #_"u32" armv6m''add_with_carry [#_"armv6m" this, #_"u32" x, #_"u32" y, #_"u32" carry_in, #_"u32" mask]
        (let [
            #_"u32" res (+ x y carry_in)
        ]
            (when-not (zero? (bit-and mask flag'Z)) #_"Zero"
                (if (zero? (bit-and res 0xffffffff))
                    (aset this i'apsr (bit-or  (aget this i'apsr)          flag'Z))
                    (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'Z)))
                )
            )

            (when-not (zero? (bit-and mask flag'N)) #_"Negative"
                (if-not (zero? (bit-and res 0x80000000))
                    (aset this i'apsr (bit-or  (aget this i'apsr)          flag'N))
                    (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'N)))
                )
            )

            (when-not (zero? (bit-and mask flag'C)) #_"Carry"
                (let [
                    #_"u64" unsigned_sum (+ (§ cast #_"u64" x) (§ cast #_"u64" y) carry_in)
                ]
                    (if (= unsigned_sum (§ cast #_"u64" res))
                        (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'C)))
                        (aset this i'apsr (bit-or  (aget this i'apsr)          flag'C))
                    )
                )
            )

            (when-not (zero? (bit-and mask flag'V)) #_"oVerflow"
                (let [
                    #_"s64" signed_sum (+ (§ cast #_"s64" (§ cast #_"s32" x)) (§ cast #_"s64" (§ cast #_"s32" y)) carry_in)
                ]
                    (if (= signed_sum (§ cast #_"s64" (§ cast #_"s32" res)))
                        (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'V)))
                        (aset this i'apsr (bit-or  (aget this i'apsr)          flag'V))
                    )
                )
            )

            (§ cast #_"u32" res)
        )
    )

    (defn #_"u32" armv6m''shift_left [#_"armv6m" this, #_"u32" word, #_"u32" shift, #_"u32" mask]
        (let [
            #_"u64" res (<< (§ cast #_"u64" word) shift)
        ]
            (when-not (zero? (bit-and mask flag'C)) #_"Carry out"
                (if-not (zero? (bit-and res (<< (§ cast #_"u64" 1) 32)))
                    (aset this i'apsr (bit-or  (aget this i'apsr)          flag'C))
                    (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'C)))
                )
            )

            (if (zero? (bit-and res 0xffffffff)) #_"Zero"
                (aset this i'apsr (bit-or  (aget this i'apsr)          flag'Z))
                (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'Z)))
            )

            (if-not (zero? (bit-and res 0x80000000)) #_"Negative"
                (aset this i'apsr (bit-or  (aget this i'apsr)          flag'N))
                (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'N)))
            )

            (§ cast #_"u32" res)
        )
    )

    (defn #_"u32" armv6m''shift_right [#_"armv6m" this, #_"u32" word, #_"u32" shift, #_"u32" mask]
        (let [
            #_"u32" res (if (< shift 32) word 0)
        ]
            (when (and (not (zero? (bit-and mask flag'C))) (pos? shift)) #_"Carry out"
                (if (and (not (zero? (bit-and word (<< 1 (dec shift))))) (<= shift 32))
                    (aset this i'apsr (bit-or  (aget this i'apsr)          flag'C))
                    (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'C)))
                )
            )

            (let [
                res (>>> res shift)
            ]
                (if (zero? (bit-and res 0xffffffff)) #_"Zero"
                    (aset this i'apsr (bit-or  (aget this i'apsr)          flag'Z))
                    (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'Z)))
                )

                (if-not (zero? (bit-and res 0x80000000)) #_"Negative"
                    (aset this i'apsr (bit-or (aget this i'apsr )          flag'N))
                    (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'N)))
                )

                res
            )
        )
    )

    (defn #_"u32" armv6m''arith_shift_right [#_"armv6m" this, #_"u32" word, #_"u32" shift, #_"u32" mask]
        (let [
            #_"s32" res (§ cast #_"s32" word)
        ]
            (when (and (not (zero? (bit-and mask flag'C))) (pos? shift)) #_"Carry out"
                (if-not (zero? (bit-and word (<< 1 (dec shift))))
                    (aset this i'apsr (bit-or  (aget this i'apsr)          flag'C))
                    (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'C)))
                )
            )

            (let [
                res (>> res shift)
            ]
                (if (zero? (bit-and res 0xffffffff)) #_"Zero"
                    (aset this i'apsr (bit-or  (aget this i'apsr)          flag'Z))
                    (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'Z)))
                )

                (if-not (zero? (bit-and res 0x80000000)) #_"Negative"
                    (aset this i'apsr (bit-or  (aget this i'apsr)          flag'N))
                    (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'N)))
                )

                res
            )
        )
    )

    (defn #_"u32" armv6m''rotate_right [#_"armv6m" this, #_"u32" word, #_"u32" shift, #_"u32" mask]
        (let [
            #_"u32" res
                (if (zero? shift)
                    word
                    (let [
                        shift (bit-and shift 0x1f)
                    ]
                        (bit-or (>>> word shift) (<< word (- 32 shift)))
                    )
                )
        ]
            (if-not (zero? (bit-and res 0x80000000)) #_"Carry out"
                (aset this i'apsr (bit-or  (aget this i'apsr)          flag'C))
                (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'C)))
            )

            (if (zero? (bit-and res 0xffffffff)) #_"Zero"
                (aset this i'apsr (bit-or  (aget this i'apsr)          flag'Z))
                (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'Z)))
            )

            (if-not (zero? (bit-and res 0x80000000)) #_"Negative"
                (aset this i'apsr (bit-or  (aget this i'apsr)          flag'N))
                (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'N)))
            )

            res
        )
    )

    (defn #_"u32" armv6m'sign_extend [#_"u32" word, #_"s32" offs]
        (if-not (zero? (bit-and word (<< 1 (dec offs))))
            (bit-or  word          (<< (bit-not 0) offs))
            (bit-and word (bit-not (<< (bit-not 0) offs)))
        )
    )

    (defn #_"u32" armv6m''exception [#_"armv6m" this, #_"u32" pc, #_"u32" exception]
        (let [
            #_"u32" sp
                (if (or (aget this i'handler?) (zero? (bit-and (aget this i'control) CONTROL_SPSEL)))
                    (aget this i'msp)
                    (aget this i'psp)
                )
            sp (- sp 4) _ (cpu''write32 this, sp, (aget this i'apsr))
            sp (- sp 4) _ (cpu''write32 this, sp, (aget this i'pc))
            sp (- sp 4) _ (cpu''write32 this, sp, (aget this i'lr))
            sp (- sp 4) _ (cpu''write32 this, sp, (aget this   12))
            sp (- sp 4) _ (cpu''write32 this, sp, (aget this    3))
            sp (- sp 4) _ (cpu''write32 this, sp, (aget this    2))
            sp (- sp 4) _ (cpu''write32 this, sp, (aget this    1))
            sp (- sp 4) _ (cpu''write32 this, sp, (aget this    0))
        ]
            (aset this i'sp sp)
            (aset this i'ipsr (bit-and exception 0x3f))
            (aset this i'pc (bit-and (cpu''read32 this, (+ (ram'base (aget this i'ram)) (<< exception 2))) (bit-not 1)))

            (cond
                (aget this i'handler?)                                (aset this i'lr 0xfffffff1) #_"Return to handler mode (recursive interrupt?)"
                (zero? (bit-and (aget this i'control) CONTROL_SPSEL)) (aset this i'lr 0xfffffff9) #_"Return to thread mode (with main stack)"
                :else                                                 (aset this i'lr 0xfffffffd) #_"Return to thread mode (with process stack)"
            )

            (aset this i'handler? true)
            (aset this i'control (bit-and (aget this i'control) (bit-not CONTROL_SPSEL)))

            (aget this i'pc)
        )
    )

    (defn #_"armv6m" armv6m''exc_return [#_"armv6m" this]
        (let [
            #_"u32" pc (aget this i'pc)
        ]
            (when (and (aget this i'handler?) (= (bit-and pc EXC_RETURN) EXC_RETURN))
                (let [
                    #_"u32" x (bit-and pc 0xf) #_"TODO: Should be 0x1f..."
                ]
                    (cond
                        (= x 0x1)
                        (do
                            (aset this i'handler? true)
                            (aset this i'control (bit-and (aget this i'control) (bit-not CONTROL_SPSEL)))
                        )
                        (= x 0x9)
                        (do
                            (aset this i'handler? false)
                            (aset this i'control (bit-and (aget this i'control) (bit-not CONTROL_SPSEL)))
                        )
                        (= x 0xd)
                        (do
                            (aset this i'handler? false)
                            (aset this i'control (bit-or (aget this i'control) CONTROL_SPSEL))
                        )
                        :else (throw! "Not handled")
                    )

                    (let [
                        #_"u32" sp (aget this i'sp)
                        _ (aset this    0 (cpu''read32 this, sp)) sp (+ sp 4)
                        _ (aset this    1 (cpu''read32 this, sp)) sp (+ sp 4)
                        _ (aset this    2 (cpu''read32 this, sp)) sp (+ sp 4)
                        _ (aset this    3 (cpu''read32 this, sp)) sp (+ sp 4)
                        _ (aset this   12 (cpu''read32 this, sp)) sp (+ sp 4)
                        _ (aset this i'lr (cpu''read32 this, sp)) sp (+ sp 4)
                        _ (aset this i'pc (cpu''read32 this, sp)) sp (+ sp 4)
                        _ (aset this i'apsr (cpu''read32 this, sp)) sp (+ sp 4)
                    ]
                        (armv6m''update_sp this, sp)
                    )
                )
            )
            this
        )
    )

    (defn #_"armv6m" armv6m''eval0 [#_"armv6m" this, #_"u16" inst]
        (let [
            #_"u32" pc (+ (aget this i'pc) 2)
            #_"u16" op (bit-and inst mask'EVAL_0)
        ]
            (cond
                (= op code'BCC) #_"BCC <label>" #_"1 1 0 1 cond imm8"
                (let [
                    #_"u32" kond (bit-and (>>> inst 8) 0x0f)
                    #_"u32" imm (bit-and (>>> inst 0) 0xff)
                    #_"u32" offs (+ (<< (armv6m'sign_extend imm, 8) 1) pc 2)
                    #_"u32" apsr (aget this i'apsr)
                    pc
                        (cond
                            (= kond  0) (if-not (zero? (bit-and apsr flag'Z)) offs pc) #_"EQ"
                            (= kond  1) (if     (zero? (bit-and apsr flag'Z)) offs pc) #_"NE"
                            (= kond  2) (if-not (zero? (bit-and apsr flag'C)) offs pc) #_"CS/HS"
                            (= kond  3) (if     (zero? (bit-and apsr flag'C)) offs pc) #_"CC/LO"
                            (= kond  4) (if-not (zero? (bit-and apsr flag'N)) offs pc) #_"MI"
                            (= kond  5) (if     (zero? (bit-and apsr flag'N)) offs pc) #_"PL"
                            (= kond  6) (if-not (zero? (bit-and apsr flag'V)) offs pc) #_"VS"
                            (= kond  7) (if     (zero? (bit-and apsr flag'V)) offs pc) #_"VC"
                            (= kond  8) (if (and (not (zero? (bit-and apsr flag'C)))     (zero? (bit-and apsr flag'Z)))  offs pc) #_"HI"
                            (= kond  9) (if (or       (zero? (bit-and apsr flag'C)) (not (zero? (bit-and apsr flag'Z)))) offs pc) #_"LS"
                            (= kond 10) (if     (= (>>> (bit-and apsr flag'N) shift'N) (>>> (bit-and apsr flag'V) shift'V)) offs pc) #_"GE"
                            (= kond 11) (if-not (= (>>> (bit-and apsr flag'N) shift'N) (>>> (bit-and apsr flag'V) shift'V)) offs pc) #_"LT"
                            (= kond 12) (if (and     (zero? (bit-and apsr flag'Z))       (= (>>> (bit-and apsr flag'N) shift'N) (>>> (bit-and apsr flag'V) shift'V)))  offs pc) #_"GT"
                            (= kond 13) (if (or (not (zero? (bit-and apsr flag'Z))) (not (= (>>> (bit-and apsr flag'N) shift'N) (>>> (bit-and apsr flag'V) shift'V)))) offs pc) #_"LE"
                            (= kond 14) offs #_"AL"
                            (= kond 15) (armv6m''exception this, pc, 11) #_"SVC"
                        )
                ]
                    (armv6m''update_pc this, pc)
                )
            )
        )
    )

    (defn #_"armv6m" armv6m''eval1 [#_"armv6m" this, #_"u16" inst]
        (let [
            #_"u32" pc (+ (aget this i'pc) 2)
            #_"u16" op (bit-and inst mask'EVAL_1)
        ]
            (cond
                (or
                    (= op code'ADDS_1) #_"ADDS <Rdn>,#<imm8>" #_"0 0 1 1 0 Rdn imm8"
                    (= op code'SUBS_1) #_"SUBS <Rdn>,#<imm8>" #_"0 0 1 1 1 Rdn imm8"
                )
                (let [
                    #_"u32" rd (bit-and (>>> inst 8) 0x7)
                    #_"u32" rn rd
                    #_"u32" imm (bit-and (>>> inst 0) 0xff)
                ]
                    (cond
                        (= op code'ADDS_1) (armv6m''update_rd this, rd, (armv6m''add_with_carry this, (aget this rn),          imm,  0, flags'all))
                        (= op code'SUBS_1) (armv6m''update_rd this, rd, (armv6m''add_with_carry this, (aget this rn), (bit-not imm), 1, flags'all))
                    )
                    (armv6m''update_pc this, pc)
                )

                (= op code'ADR) #_"ADR <Rd>,<label>" #_"1 0 1 0 0 Rd imm8"
                (let [
                    #_"u32" rd (bit-and (>>> inst 8) 0x7)
                    #_"u32" imm (bit-and (>>> inst 0) 0xff)
                ]
                    (armv6m''update_rd this, rd, (+ pc imm 2))
                    (armv6m''update_pc this, pc)
                )

                (= op code'MOVS) #_"MOVS <Rd>,#<imm8>" #_"0 0 1 0 0 Rd imm8"
                (let [
                    #_"u32" rd (bit-and (>>> inst 8) 0x7)
                    #_"u32" imm (bit-and (>>> inst 0) 0xff)
                ]
                    (armv6m''update_rd this, rd, imm)
                    (armv6m''update_nz this, imm)
                    (armv6m''update_pc this, pc)
                )

                (or
                    (= op code'ASRS) #_"ASRS <Rd>,<Rm>,#<imm5>" #_"0 0 0 1 0 imm5 Rm Rd"
                    (= op code'LSRS) #_"LSRS <Rd>,<Rm>,#<imm5>" #_"0 0 0 0 1 imm5 Rm Rd"
                )
                (let [
                    #_"u32" imm (bit-and (>>> inst 6) 0x1f)
                    #_"u32" rm (bit-and (>>> inst 3) 0x7)
                    #_"u32" rd (bit-and (>>> inst 0) 0x7)
                    imm (if (zero? imm) 32 imm)
                ]
                    (cond
                        (= op code'ASRS) (armv6m''update_rd this, rd, (armv6m''arith_shift_right this, (aget this rm), imm, flags'NZC))
                        (= op code'LSRS) (armv6m''update_rd this, rd, (armv6m''shift_right       this, (aget this rm), imm, flags'NZC))
                    )
                    (armv6m''update_pc this, pc)
                )

                (or
                    (= op code'MOVS_1) #_"MOVS <Rd>,<Rm>"         #_"0 0 0 0 0 0 0 0 0 0 Rm Rd"
                    (= op code'LSLS)   #_"LSLS <Rd>,<Rm>,#<imm5>" #_"0 0 0 0 0 imm5 Rm Rd"
                )
                (let [
                    #_"u32" imm (bit-and (>>> inst 6) 0x1f)
                    #_"u32" rm (bit-and (>>> inst 3) 0x7)
                    #_"u32" rd (bit-and (>>> inst 0) 0x7)
                ]
                    (if (zero? imm)
                        (do
                            (armv6m''update_rd this, rd, (aget this rm))
                            (armv6m''update_nz this, (aget this rm))
                        )
                        (do
                            (armv6m''update_rd this, rd, (armv6m''shift_left this, (aget this rm), imm, flags'NZC))
                        )
                    )
                    (armv6m''update_pc this, pc)
                )

                (= op code'B) #_"B <label>" #_"1 1 1 0 0 imm11"
                (let [
                    #_"u32" imm (bit-and (>>> inst 0) 0x7ff)
                ]
                    (armv6m''update_pc this, (+ (<< (armv6m'sign_extend imm, 11) 1) pc 2))
                )

                (= op code'BL) #_"BL <label>" #_"1 1 1 0 1 S imm10 1 1 J1 1 J2 imm11"
                (let [
                    #_"u16" inst2 (armv6m''fetch this, pc)
                ]
                    (when (= (bit-and inst2 0xc000) 0xc000)
                        (let [
                            #_"u32" imm (bit-and (>>> inst 0) 0x7ff)
                            #_"u32" offs (+ pc (<< (bit-or (<< (armv6m'sign_extend imm, 11) 11) (bit-and inst2 0x7ff)) 1))
                        ]
                            (armv6m''update_rd this, i'lr, (bit-or (+ pc 2) 1))
                            (armv6m''update_pc this, (+ offs 2))
                        )
                    )
                )

                (= op code'CMP) #_"CMP <Rn>,#<imm8>" #_"0 0 1 0 1 Rn imm8"
                (let [
                    #_"u32" rn (bit-and (>>> inst 8) 0x7)
                    #_"u32" imm (bit-and (>>> inst 0) 0xff)
                ]
                    (armv6m''add_with_carry this, (aget this rn), (bit-not imm), 1, flags'all)
                    (armv6m''update_pc this, pc)
                )

                (or
                    (= op code'LDM)   #_"LDM <Rn>!,<registers> <Rn> not included in <registers>" #_"1 1 0 0 1 Rn register_list"
                    (= op code'LDM_1) #_"LDM <Rn>,<registers> <Rn> included in <registers>"      #_"1 1 0 0 1 Rn register_list"
                )
                (let [
                    #_"u32" rn (bit-and (>>> inst 8) 0x7)
                    #_"u32" rd rn
                    #_"u32" regs (bit-and (>>> inst 0) 0xff)
                ]
                    (loop [pc pc #_"u32" addr (aget this rn) regs regs #_"s32" i 0]
                        (if (and (< i size'regfile) (not (zero? regs)))
                            (if-not (zero? (bit-and regs (<< 1 i)))
                                (let [
                                    _ (aset this i (cpu''read32 this, addr))
                                    pc
                                        (if (= i i'pc)
                                            (do
                                                (when-not (= (bit-and (aget this i'pc) EXC_RETURN) EXC_RETURN)
                                                    (armv6m''update_pc this, (bit-and (aget this i'pc) (bit-not 1)))
                                                )
                                                (aget this i'pc)
                                            )
                                            pc
                                        )
                                ]
                                    (recur pc (+ addr 4) (bit-and regs (bit-not (<< 1 i))) (inc i))
                                )
                                (recur pc addr regs (inc i))
                            )
                            (do
                                (assert (not (= rd i'pc)))
                                (aset this rd addr)
                                (armv6m''update_pc this, pc)
                            )
                        )
                    )
                )

                (= op code'STM) #_"STM <Rn>!,<registers>" #_"1 1 0 0 0 Rn register_list"
                (let [
                    #_"u32" rn (bit-and (>>> inst 8) 0x7)
                    #_"u32" rd rn
                    #_"u32" regs (bit-and (>>> inst 0) 0xff)
                ]
                    (loop [#_"u32" addr (aget this rn) regs regs #_"s32" i 0]
                        (if (and (< i size'regfile) (not (zero? regs)))
                            (if-not (zero? (bit-and regs (<< 1 i)))
                                (do
                                    (cpu''write32 this, addr, (aget this i))
                                    (recur (+ addr 4) (bit-and regs (bit-not (<< 1 i))) (inc i))
                                )
                                (recur addr regs (inc i))
                            )
                            (do
                                (armv6m''update_rd this, rd, addr)
                                (armv6m''update_pc this, pc)
                            )
                        )
                    )
                )

                (or
                    (= op code'LDR)  #_"LDR  <Rt>,[<Rn>{,#<imm5>}]" #_"0 1 1 0 1 imm5 Rn Rt"
                    (= op code'LDRB) #_"LDRB <Rt>,[<Rn>{,#<imm5>}]" #_"0 1 1 1 1 imm5 Rn Rt"
                    (= op code'LDRH) #_"LDRH <Rt>,[<Rn>{,#<imm5>}]" #_"1 0 0 0 1 imm5 Rn Rt"
                    (= op code'STR)  #_"STR  <Rt>,[<Rn>{,#<imm5>}]" #_"0 1 1 0 0 imm5 Rn Rt"
                    (= op code'STRB) #_"STRB <Rt>,[<Rn>,#<imm5>]"   #_"0 1 1 1 0 imm5 Rn Rt"
                    (= op code'STRH) #_"STRH <Rt>,[<Rn>{,#<imm5>}]" #_"1 0 0 0 0 imm5 Rn Rt"
                )
                (let [
                    #_"u32" imm (bit-and (>>> inst 6) 0x1f)
                    #_"u32" rn (bit-and (>>> inst 3) 0x7)
                    #_"u32" rt (bit-and (>>> inst 0) 0x7)
                ]
                    (cond
                        (= op code'LDR) (do (aset this rt (cpu''read32  this, (+ (aget this rn) (<< imm 2)))) (assert (not (= rt i'pc))))
                        (= op code'LDRB)    (aset this rt (cpu''read8   this, (+ (aget this rn)     imm)))
                        (= op code'LDRH)    (aset this rt (cpu''read16  this, (+ (aget this rn) (<< imm 1))))
                        (= op code'STR)                   (cpu''write32 this, (+ (aget this rn) (<< imm 2)), (aget this rt))
                        (= op code'STRB)                  (cpu''write8  this, (+ (aget this rn)     imm),    (aget this rt))
                        (= op code'STRH)                  (cpu''write16 this, (+ (aget this rn) (<< imm 1)), (aget this rt))
                    )
                    (armv6m''update_pc this, pc)
                )

                (= op code'LDR_2) #_"LDR <Rt>,<label>" #_"0 1 0 0 1 Rt imm8"
                (let [
                    #_"u32" rt (bit-and (>>> inst 8) 0x7)
                    #_"u32" imm (bit-and (>>> inst 0) 0xff)
                ]
                    (assert (not (= rt i'pc)))
                    (aset this rt (cpu''read32 this, (+ (bit-and (aget this i'pc) 0xfffffffc) (<< imm 2) 4)))
                    (armv6m''update_pc this, pc)
                )

                (or
                    (= op code'LDR_1) #_"LDR <Rt>,[SP{,#<imm8>}]" #_"1 0 0 1 1 Rt imm8"
                    (= op code'STR_1) #_"STR <Rt>,[SP,#<imm8>]"   #_"1 0 0 1 0 Rt imm8"
                    (= op code'ADD_1) #_"ADD <Rd>,SP,#<imm8>"     #_"1 0 1 0 1 Rd imm8"
                )
                (let [
                    #_"u32" rt (bit-and (>>> inst 8) 0x7)
                    #_"u32" rd rt
                    #_"u32" imm (bit-and (>>> inst 0) 0xff)
                ]
                    (cond
                        (= op code'LDR_1) (do (aset this rt (cpu''read32  this, (+ (aget this i'sp) (<< imm 2)))) (assert (not (= rt i'pc))))
                        (= op code'STR_1)                   (cpu''write32 this, (+ (aget this i'sp) (<< imm 2)), (aget this rt))
                        (= op code'ADD_1)          (armv6m''update_rd this, rd, (+ (aget this i'sp) (<< imm 2)))
                    )
                    (armv6m''update_pc this, pc)
                )
            )
        )
    )

    (defn #_"armv6m" armv6m''eval2 [#_"armv6m" this, #_"u16" inst]
        (let [
            #_"u32" pc (+ (aget this i'pc) 2)
            #_"u16" op (bit-and inst mask'EVAL_2)
        ]
            (cond
                (or
                    (= op code'ADDS) #_"ADDS <Rd>,<Rn>,#<imm3>" #_"0 0 0 1 1 1 0 imm3 Rn Rd"
                    (= op code'SUBS) #_"SUBS <Rd>,<Rn>,#<imm3>" #_"0 0 0 1 1 1 1 imm3 Rn Rd"
                )
                (let [
                    #_"u32" imm (bit-and (>>> inst 6) 0x7)
                    #_"u32" rn (bit-and (>>> inst 3) 0x7)
                    #_"u32" rd (bit-and (>>> inst 0) 0x7)
                ]
                    (cond
                        (= op code'ADDS) (armv6m''update_rd this, rd, (armv6m''add_with_carry this, (aget this rn),          imm,  0, flags'all))
                        (= op code'SUBS) (armv6m''update_rd this, rd, (armv6m''add_with_carry this, (aget this rn), (bit-not imm), 1, flags'all))
                    )
                    (armv6m''update_pc this, pc)
                )

                (or
                    (= op code'ADDS_2) #_"ADDS <Rd>,<Rn>,<Rm>" #_"0 0 0 1 1 0 0 Rm Rn Rd"
                    (= op code'SUBS_2) #_"SUBS <Rd>,<Rn>,<Rm>" #_"0 0 0 1 1 0 1 Rm Rn Rd"
                )
                (let [
                    #_"u32" rm (bit-and (>>> inst 6) 0x7)
                    #_"u32" rn (bit-and (>>> inst 3) 0x7)
                    #_"u32" rd (bit-and (>>> inst 0) 0x7)
                ]
                    (cond
                        (= op code'ADDS_2) (armv6m''update_rd this, rd, (armv6m''add_with_carry this, (aget this rn),          (aget this rm),  0, flags'all))
                        (= op code'SUBS_2) (armv6m''update_rd this, rd, (armv6m''add_with_carry this, (aget this rn), (bit-not (aget this rm)), 1, flags'all))
                    )
                    (armv6m''update_pc this, pc)
                )

                (or
                    (= op code'LDR_3)  #_"LDR   <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 1 0 0 Rm Rn Rt"
                    (= op code'LDRB_1) #_"LDRB  <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 1 1 0 Rm Rn Rt"
                    (= op code'LDRH_1) #_"LDRH  <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 1 0 1 Rm Rn Rt"
                    (= op code'LDRSB)  #_"LDRSB <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 0 1 1 Rm Rn Rt"
                    (= op code'LDRSH)  #_"LDRSH <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 1 1 1 Rm Rn Rt"
                    (= op code'STR_2)  #_"STR   <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 0 0 0 Rm Rn Rt"
                    (= op code'STRB_1) #_"STRB  <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 0 1 0 Rm Rn Rt"
                    (= op code'STRH_1) #_"STRH  <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 0 0 1 Rm Rn Rt"
                )
                (let [
                    #_"u32" rm (bit-and (>>> inst 6) 0x7)
                    #_"u32" rn (bit-and (>>> inst 3) 0x7)
                    #_"u32" rt (bit-and (>>> inst 0) 0x7)
                    #_"u32" rd rt
                ]
                    (cond
                        (= op code'LDR_3) (do (aset this rt                     (cpu''read32  this, (+ (aget this rn) (aget this rm)))) (assert (not (= rt i'pc))))
                        (= op code'LDRB_1)    (aset this rt                     (cpu''read8   this, (+ (aget this rn) (aget this rm))))
                        (= op code'LDRH_1)    (aset this rt                     (cpu''read16  this, (+ (aget this rn) (aget this rm))))
                        (= op code'LDRSB)     (aset this rt (armv6m'sign_extend (cpu''read8   this, (+ (aget this rn) (aget this rm))),  8))
                        (= op code'LDRSH)     (aset this rt (armv6m'sign_extend (cpu''read16  this, (+ (aget this rn) (aget this rm))), 16))
                        (= op code'STR_2)                                       (cpu''write32 this, (+ (aget this rn) (aget this rm)), (aget this rt))
                        (= op code'STRB_1)                                      (cpu''write8  this, (+ (aget this rn) (aget this rm)), (aget this rt))
                        (= op code'STRH_1)                                      (cpu''write16 this, (+ (aget this rn) (aget this rm)), (aget this rt))
                    )
                    (armv6m''update_pc this, pc)
                )

                (= op code'POP) #_"POP <registers>" #_"1 0 1 1 1 1 0 P register_list"
                (let [
                    #_"u32" regs (bit-and (>>> inst 0) 0xff)
                    regs (if-not (zero? (bit-and inst (<< 1 8))) (bit-or regs (<< 1 i'pc)) regs)
                ]
                    (loop [pc pc #_"u32" sp (aget this i'sp) regs regs #_"s32" i 0]
                        (if (and (< i size'regfile) (not (zero? regs)))
                            (if-not (zero? (bit-and regs (<< 1 i)))
                                (let [
                                    _ (aset this i (cpu''read32 this, sp))
                                    pc
                                        (if (= i i'pc)
                                            (do
                                                (when-not (= (bit-and (aget this i'pc) EXC_RETURN) EXC_RETURN)
                                                    (armv6m''update_pc this, (bit-and (aget this i'pc) (bit-not 1)))
                                                )
                                                (aget this i'pc)
                                            )
                                            pc
                                        )
                                ]
                                    (recur pc (+ sp 4) (bit-and regs (bit-not (<< 1 i))) (inc i))
                                )
                                (recur pc sp regs (inc i))
                            )
                            (do
                                (armv6m''update_sp this, sp)
                                (armv6m''update_pc this, pc)
                            )
                        )
                    )
                )

                (= op code'PUSH) #_"PUSH <registers>" #_"1 0 1 1 0 1 0 M register_list"
                (let [
                    #_"u32" regs (bit-and (>>> inst 0) 0xff)
                    regs (if-not (zero? (bit-and inst (<< 1 8))) (bit-or regs (<< 1 i'lr)) regs)
                    #_"s32" n
                        (loop [n 0 #_"s32" i 0]
                            (if (< i size'regfile)
                                (recur (if-not (zero? (bit-and regs (<< 1 i))) (inc n) n) (inc i))
                                n
                            )
                        )
                ]
                    (loop [#_"u32" sp (aget this i'sp) #_"u32" addr (- sp (<< n 2)) regs regs #_"s32" i 0]
                        (if (and (< i size'regfile) (not (zero? regs)))
                            (if-not (zero? (bit-and regs (<< 1 i)))
                                (do
                                    (cpu''write32 this, addr, (aget this i))
                                    (recur (- sp 4) (+ addr 4) (bit-and regs (bit-not (<< 1 i))) (inc i))
                                )
                                (recur sp addr regs (inc i))
                            )
                            (do
                                (armv6m''update_sp this, sp)
                                (armv6m''update_pc this, pc)
                            )
                        )
                    )
                )
            )
        )
    )

    (defn #_"armv6m" armv6m''eval3 [#_"armv6m" this, #_"u16" inst]
        (let [
            #_"u32" pc (+ (aget this i'pc) 2)
            #_"u16" op (bit-and inst mask'EVAL_3)
        ]
            (cond
                (= op code'ADD) #_"ADD <Rdn>,<Rm>" #_"0 1 0 0 0 1 0 0 Rm Rdn"
                (let [
                    #_"u32" rm (bit-and (>>> inst 3) 0xf)
                    #_"u32" rd (bit-or (bit-and (>>> inst 4) 0x8) (bit-and (>>> inst 0) 0x7))
                    #_"u32" rn rd
                ]
                    (armv6m''update_rd this, rd, (+ (aget this rn) (aget this rm)))
                    (armv6m''update_pc this, pc)
                )

                (or
                    (= op code'BKPT) #_"BKPT #<imm8>" #_"1 0 1 1 1 1 1 0 imm8"
                    (= op code'SVC) #_"SVC #<imm8>" #_"1 1 0 1 1 1 1 1 imm8"
                    (= op code'UDF) #_"UDF #<imm8>" #_"1 1 0 1 1 1 1 0 imm8"
                )
                (let [
                    #_"u32" imm (bit-and (>>> inst 0) 0xff)
                ]
                    (armv6m''update_pc this, (if (= op code'SVC) (armv6m''exception this, pc, 11) pc))
                )

                (= op code'CMP_2) #_"CMP <Rn>,<Rm> <Rn> and <Rm> not both from R0-R7" #_"0 1 0 0 0 1 0 1 N Rm Rn"
                (let [
                    #_"u32" rm (bit-and (>>> inst 3) 0xf)
                    #_"u32" rn (bit-or (bit-and (>>> inst 4) 0x8) (bit-and (>>> inst 0) 0x7))
                ]
                    (armv6m''add_with_carry this, (aget this rn), (bit-not (aget this rm)), 1, flags'all)
                    (armv6m''update_pc this, pc)
                )

                (= op code'MOV) #_"MOV <Rd>,<Rm> Otherwise all versions of the Thumb instruction set." #_"0 1 0 0 0 1 1 0 D Rm Rd"
                (let [
                    #_"u32" rm (bit-and (>>> inst 3) 0xf)
                    #_"u32" rd (bit-or (bit-and (>>> inst 4) 0x8) (bit-and (>>> inst 0) 0x7))
                ]
                    (if (= rd i'pc)
                        (do
                            (armv6m''update_pc this, (bit-and (aget this rm) (bit-not 1)))
                        )
                        (do
                            (armv6m''update_rd this, rd, (aget this rm))
                            (armv6m''update_pc this, pc)
                        )
                    )
                    this
                )
            )
        )
    )

    (defn #_"armv6m" armv6m''eval4 [#_"armv6m" this, #_"u16" inst]
        (let [
            #_"u32" pc (+ (aget this i'pc) 2)
            #_"u16" op (bit-and inst mask'EVAL_4)
        ]
            (cond
                (or
                    (= op code'ADD_2) #_"ADD SP,SP,#<imm7>" #_"1 0 1 1 0 0 0 0 0 imm7"
                    (= op code'SUB)   #_"SUB SP,SP,#<imm7>" #_"1 0 1 1 0 0 0 0 1 imm7"
                )
                (let [
                    #_"u32" imm (bit-and (>>> inst 0) 0x7f)
                ]
                    (cond
                        (= op code'ADD_2) (armv6m''update_sp this, (+ (aget this i'sp) (<< imm 2)))
                        (= op code'SUB)   (armv6m''update_sp this, (- (aget this i'sp) (<< imm 2)))
                    )
                    (armv6m''update_pc this, pc)
                )

                (= op code'BLX) #_"BLX <Rm>" #_"0 1 0 0 0 1 1 1 1 Rm (0) (0) (0)"
                (let [
                    #_"u32" rm (bit-and (>>> inst 3) 0xf)
                ]
                    (armv6m''update_rd this, i'lr, (bit-or pc 1))
                    (armv6m''update_pc this, (bit-and (aget this rm) (bit-not 1)))
                )

                (= op code'BX) #_"BX <Rm>" #_"0 1 0 0 0 1 1 1 0 Rm (0) (0) (0)"
                (let [
                    #_"u32" rm (bit-and (>>> inst 3) 0xf)
                ]
                    (armv6m''update_pc this, (bit-and (aget this rm) (bit-not 1)))
                )
            )
        )
    )

    (defn #_"armv6m" armv6m''eval5 [#_"armv6m" this, #_"u16" inst]
        (let [
            #_"u32" pc (+ (aget this i'pc) 2)
            #_"u16" op (bit-and inst mask'EVAL_5)
        ]
            (cond
                (or
                    (= op code'ADCS) #_"ADCS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 1 0 1 Rm Rdn"
                    (= op code'SBCS) #_"SBCS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 1 1 0 Rm Rdn"
                )
                (let [
                    #_"u32" rm (bit-and (>>> inst 3) 0x7)
                    #_"u32" rd (bit-and (>>> inst 0) 0x7)
                    #_"u32" rn rd
                ]
                    (cond
                        (= op code'ADCS) (armv6m''update_rd this, rd, (armv6m''add_with_carry this, (aget this rn),          (aget this rm),  (if (zero? (bit-and (aget this i'apsr) flag'C)) 0 1), flags'all))
                        (= op code'SBCS) (armv6m''update_rd this, rd, (armv6m''add_with_carry this, (aget this rn), (bit-not (aget this rm)), (if (zero? (bit-and (aget this i'apsr) flag'C)) 0 1), flags'all))
                    )
                    (armv6m''update_pc this, pc)
                )

                (or
                    (= op code'ANDS) #_"ANDS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 0 0 0 Rm Rdn"
                    (= op code'BICS) #_"BICS <Rdn>,<Rm>" #_"0 1 0 0 0 0 1 1 1 0 Rm Rdn"
                    (= op code'EORS) #_"EORS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 0 0 1 Rm Rdn"
                    (= op code'ORRS) #_"ORRS <Rdn>,<Rm>" #_"0 1 0 0 0 0 1 1 0 0 Rm Rdn"
                )
                (let [
                    #_"u32" rm (bit-and (>>> inst 3) 0x7)
                    #_"u32" rd (bit-and (>>> inst 0) 0x7)
                    #_"u32" rn rd
                    #_"u32" word
                        (cond
                            (= op code'ANDS) (bit-and (aget this rn)          (aget this rm))
                            (= op code'BICS) (bit-and (aget this rn) (bit-not (aget this rm)))
                            (= op code'EORS) (bit-xor (aget this rn)          (aget this rm))
                            (= op code'ORRS) (bit-or  (aget this rn)          (aget this rm))
                        )
                ]
                    (armv6m''update_rd this, rd, word)
                    (armv6m''update_nz this, word)
                    (armv6m''update_pc this, pc)
                )

                (or
                    (= op code'ASRS_1) #_"ASRS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 1 0 0 Rm Rdn"
                    (= op code'LSRS_1) #_"LSRS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 0 1 1 Rm Rdn"
                    (= op code'RORS)   #_"RORS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 1 1 1 Rm Rdn"
                )
                (let [
                    #_"u32" rm (bit-and (>>> inst 3) 0x7)
                    #_"u32" rd (bit-and (>>> inst 0) 0x7)
                    #_"u32" rn rd
                ]
                    (cond
                        (= op code'ASRS_1) (armv6m''update_rd this, rd, (armv6m''arith_shift_right this, (aget this rn),          (aget this rm),       flags'NZC))
                        (= op code'LSRS_1) (armv6m''update_rd this, rd, (armv6m''shift_right       this, (aget this rn), (bit-and (aget this rm) 0xff), flags'NZC))
                        (= op code'RORS)   (armv6m''update_rd this, rd, (armv6m''rotate_right      this, (aget this rn), (bit-and (aget this rm) 0xff), flags'NZC))
                    )
                    (armv6m''update_pc this, pc)
                )

                (= op code'LSLS_1) #_"LSLS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 0 1 0 Rm Rdn"
                (let [
                    #_"u32" rm (bit-and (>>> inst 3) 0x7)
                    #_"u32" rd (bit-and (>>> inst 0) 0x7)
                    #_"u32" rn rd
                ]
                    (if (zero? (aget this rm))
                        (do
                            (armv6m''update_rd this, rd, (aget this rn))
                            (armv6m''update_nz this, (aget this rn))
                        )
                        (do
                            (armv6m''update_rd this, rd, (armv6m''shift_left this, (aget this rn), (aget this rm), flags'NZC))
                        )
                    )
                    (armv6m''update_pc this, pc)
                )

                (or
                    (= op code'CMN)   #_"CMN <Rn>,<Rm>"                               #_"0 1 0 0 0 0 1 0 1 1 Rm Rn"
                    (= op code'CMP_1) #_"CMP <Rn>,<Rm> <Rn> and <Rm> both from R0-R7" #_"0 1 0 0 0 0 1 0 1 0 Rm Rn"
                    (= op code'TST)   #_"TST <Rn>,<Rm>"                               #_"0 0 0 1 0 0 1 0 0 0 Rm Rn"
                )
                (let [
                    #_"u32" rm (bit-and (>>> inst 3) 0x7)
                    #_"u32" rn (bit-and (>>> inst 0) 0x7)
                ]
                    (cond
                        (= op code'CMN)   (armv6m''add_with_carry this,          (aget this rn),          (aget this rm),  0, flags'all)
                        (= op code'CMP_1) (armv6m''add_with_carry this,          (aget this rn), (bit-not (aget this rm)), 1, flags'all)
                        (= op code'TST)   (armv6m''update_nz      this, (bit-and (aget this rn)           (aget this rm)))
                    )
                    (armv6m''update_pc this, pc)
                )

                (= op code'MULS) #_"MULS <Rdm>,<Rn>,<Rdm>" #_"0 1 0 0 0 0 1 1 0 1 Rn Rdm"
                (let [
                    #_"u32" rn (bit-and (>>> inst 3) 0x7)
                    #_"u32" rd (bit-and (>>> inst 0) 0x7)
                    #_"u32" rm rd
                    #_"u32" word (* (aget this rn) (aget this rm))
                ]
                    (armv6m''update_rd this, rd, word)
                    (armv6m''update_nz this, word)
                    (armv6m''update_pc this, pc)
                )

                (= op code'MVNS) #_"MVNS <Rd>,<Rm>" #_"0 1 0 0 0 0 1 1 1 1 Rm Rd"
                (let [
                    #_"u32" rm (bit-and (>>> inst 3) 0x7)
                    #_"u32" rd (bit-and (>>> inst 0) 0x7)
                    #_"u32" word (bit-not (aget this rm))
                ]
                    (armv6m''update_rd this, rd, word)
                    (armv6m''update_nz this, word)
                    (armv6m''update_pc this, pc)
                )

                (or
                    (= op code'REV)   #_"REV   <Rd>,<Rm>" #_"1 0 1 1 1 0 1 0 0 0 Rm Rd"
                    (= op code'REV16) #_"REV16 <Rd>,<Rm>" #_"1 0 1 1 1 0 1 0 0 1 Rm Rd"
                    (= op code'REVSH) #_"REVSH <Rd>,<Rm>" #_"1 0 1 1 1 0 1 0 1 1 Rm Rd"
                )
                (let [
                    #_"u32" rm (bit-and (>>> inst 3) 0x7)
                    #_"u32" rd (bit-and (>>> inst 0) 0x7)
                ]
                    (cond
                        (= op code'REV)
                            (armv6m''update_rd this, rd,
                                (bit-or
                                    (<< (bit-and (>>> (aget this rm)  0) 0xff) 24)
                                    (<< (bit-and (>>> (aget this rm)  8) 0xff) 16)
                                    (<< (bit-and (>>> (aget this rm) 16) 0xff)  8)
                                    (<< (bit-and (>>> (aget this rm) 24) 0xff)  0)
                                )
                            )
                        (= op code'REV16)
                            (armv6m''update_rd this, rd,
                                (bit-or
                                    (<< (bit-and (>>> (aget this rm)  0) 0xff)  8)
                                    (<< (bit-and (>>> (aget this rm)  8) 0xff)  0)
                                    (<< (bit-and (>>> (aget this rm) 16) 0xff) 24)
                                    (<< (bit-and (>>> (aget this rm) 24) 0xff) 16)
                                )
                            )
                        (= op code'REVSH)
                            (armv6m''update_rd this, rd, (armv6m'sign_extend (bit-or (<< (bit-and (>>> (aget this rm) 0) 0xff) 8) (<< (bit-and (>>> (aget this rm) 8) 0xff) 0)), 16))
                    )
                    (armv6m''update_pc this, pc)
                )

                (or
                    (= op code'SXTB) #_"SXTB <Rd>,<Rm>" #_"1 0 1 1 1 0 0 0 0 1 Rm Rd"
                    (= op code'SXTH) #_"SXTH <Rd>,<Rm>" #_"1 0 1 1 1 0 0 0 0 0 Rm Rd"
                    (= op code'UXTB) #_"UXTB <Rd>,<Rm>" #_"1 0 1 1 1 0 0 0 1 1 Rm Rd"
                    (= op code'UXTH) #_"UXTH <Rd>,<Rm>" #_"1 0 1 1 1 0 0 0 1 0 Rm Rd"
                )
                (let [
                    #_"u32" rm (bit-and (>>> inst 3) 0x7)
                    #_"u32" rd (bit-and (>>> inst 0) 0x7)
                ]
                    (cond
                        (= op code'SXTB)
                            (let [
                                #_"u32" word (bit-and (aget this rm) 0xff)
                            ]
                                (armv6m''update_rd this, rd, (if-not (zero? (bit-and word 0x80)) (bit-or word (<< (bit-not 0) 8)) word))
                            )
                        (= op code'SXTH)
                            (let [
                                #_"u32" word (bit-and (aget this rm) 0xffff)
                            ]
                                (armv6m''update_rd this, rd, (if-not (zero? (bit-and word 0x8000)) (bit-or word (<< (bit-not 0) 16)) word))
                            )
                        (= op code'UXTB) (armv6m''update_rd this, rd, (bit-and (aget this rm) 0xff))
                        (= op code'UXTH) (armv6m''update_rd this, rd, (bit-and (aget this rm) 0xffff))
                    )
                    (armv6m''update_pc this, pc)
                )

                (= op code'RSBS) #_"RSBS <Rd>,<Rn>,#0" #_"0 1 0 0 0 0 1 0 0 1 Rn Rd"
                (let [
                    #_"u32" rn (bit-and (>>> inst 3) 0x7)
                    #_"u32" rd (bit-and (>>> inst 0) 0x7)
                ]
                    (armv6m''update_rd this, rd, (armv6m''add_with_carry this, (bit-not (aget this rn)), 0, 1, flags'all))
                    (armv6m''update_pc this, pc)
                )
            )
        )
    )

    (defn #_"armv6m" armv6m''eval6 [#_"armv6m" this, #_"u16" inst]
        (let [
            #_"u32" pc (+ (aget this i'pc) 2)
            #_"u16" op (bit-and inst mask'EVAL_6)
        ]
            (cond
                (= op code'MRS) #_"MRS <Rd>,<spec_reg>" #_"1 1 1 0 1 0 1 1 1 1 1 (0) (1) (1) (1) (1) 1 0 (0) 0 Rd SYSm"
                (let [
                    #_"u16" inst2 (armv6m''fetch this, pc)
                    #_"u32" sysm (bit-and inst2 0xff)
                    #_"u32" rd (bit-and (>>> inst2 8) 0xf)
                    #_"u32" x (bit-and (>>> sysm 3) 0x1f)
                ]
                    (cond
                        (= x 0)
                        (let [
                            #_"u32" word 0
                            word (if-not (zero? (bit-and sysm 0x1)) (bit-or word (bit-and (aget this i'ipsr)      0x1ff)) word)
                            word (if     (zero? (bit-and sysm 0x4)) (bit-or word (bit-and (aget this i'apsr) 0xf8000000)) word)
                        ]
                            (armv6m''update_rd this, rd, (bit-or word (aget this i'ipsr) (aget this i'epsr)))
                        )
                        (= x 1)
                        (let [
                            #_"u32" y (bit-and sysm 0x7)
                        ]
                            (cond
                                (= y 0) (armv6m''update_rd this, rd, (aget this i'msp))
                                (= y 1) (armv6m''update_rd this, rd, (aget this i'psp))
                            )
                        )
                        (= x 2)
                        (let [
                            #_"u32" y (bit-and sysm 0x7)
                        ]
                            (cond
                                (= y 0) (armv6m''update_rd this, rd, (bit-and (aget this i'primask) PRIMASK_PM))
                                (= y 4) (armv6m''update_rd this, rd, (bit-and (aget this i'control) CONTROL_MASK))
                            )
                        )
                    )
                    (armv6m''update_pc this, (+ pc 2))
                )

                (= op code'MSR) #_"MSR <spec_reg>,<Rn>" #_"1 1 1 0 1 0 1 1 1 0 0 (0) Rn 1 0 (0) 0 (1) (0) (0) (0) SYSm"
                (let [
                    #_"u32" rn (bit-and (>>> inst 0) 0xf)
                    #_"u16" inst2 (armv6m''fetch this, pc)
                    #_"u32" sysm (bit-and inst2 0xff)
                    #_"u32" x (bit-and (>>> sysm 3) 0x1f)
                ]
                    (cond
                        (= x 0)
                        (do
                            (when (zero? (bit-and sysm 0x4))
                                (aset this i'apsr (bit-and (aget this rn) 0xf8000000))
                            )
                        )
                        (= x 1)
                        (let [
                            #_"u32" y (bit-and sysm 0x7)
                        ]
                            (cond #_"TODO: Only if privileged..."
                                (= y 0) (aset this i'msp (aget this rn))
                                (= y 1) (aset this i'psp (aget this rn))
                            )
                        )
                        (= x 2)
                        (let [
                            #_"u32" y (bit-and sysm 0x7)
                        ]
                            (cond #_"TODO: Only if privileged..."
                                (= y 0)
                                (do
                                    (aset this i'primask (bit-and (aget this rn) PRIMASK_PM))
                                )
                                (= y 4)
                                (do
                                    (when-not (aget this i'handler?)
                                        (aset this i'control (bit-and (aget this rn) CONTROL_MASK))
                                    )
                                )
                            )
                        )
                    )
                    (armv6m''update_pc this, (+ pc 2))
                )

                (= op code'CPS) #_"CPS<effect> i" #_"1 0 1 1 0 1 1 0 0 1 1 im (0) (0) (1) (0)"
                (let [
                    #_"u32" imm (bit-and (>>> inst 4) 0x1)
                ]
                    (if (zero? imm) #_"TODO: Only if privileged..."
                        (aset this i'primask (bit-and (aget this i'primask) (bit-not PRIMASK_PM))) #_"Enable"
                        (aset this i'primask (bit-or  (aget this i'primask)          PRIMASK_PM))  #_"Disable"
                    )
                    (armv6m''update_pc this, pc)
                )
            )
        )
    )

    (defn #_"armv6m" armv6m''eval7 [#_"armv6m" this, #_"u16" inst]
        (let [
            #_"u32" pc (+ (aget this i'pc) 2)
            #_"u16" op (bit-and inst mask'EVAL_7)
        ]
            (cond
                (or
                    (= op code'DMB)   #_"DMB #<option>"  #_"1 1 1 0 1 0 1 1 1 0 1 1 (1) (1) (1) (1) 1 0 (0) 0 (1) (1) (1) (1) 0 1 0 1 option"
                    (= op code'DSB)   #_"DSB #<option>"  #_"1 1 1 0 1 0 1 1 1 0 1 1 (1) (1) (1) (1) 1 0 (0) 0 (1) (1) (1) (1) 0 1 0 0 option"
                    (= op code'ISB)   #_"ISB #<option>"  #_"1 1 1 0 1 0 1 1 1 0 1 1 (1) (1) (1) (1) 1 0 (0) 0 (1) (1) (1) (1) 0 1 1 0 option"
                    (= op code'UDF_W) #_"UDF_W #<imm16>" #_"1 1 1 1 0 1 1 1 1 1 1 1 imm4 1 0 1 0 imm12"
                )
                (do
                    (armv6m''update_pc this, (+ pc 2))
                )
            )
        )
    )

    (defn #_"armv6m" armv6m''eval8 [#_"armv6m" this, #_"u16" inst]
        (let [
            #_"u32" pc (+ (aget this i'pc) 2)
            #_"u16" op (bit-and inst mask'EVAL_8)
        ]
            (cond
                (or
                    (= op code'NOP)   #_"NOP"   #_"1 0 1 1 1 1 1 1 0 0 0 0 0 0 0 0"
                    (= op code'SEV)   #_"SEV"   #_"1 0 1 1 1 1 1 1 0 1 0 0 0 0 0 0"
                    (= op code'WFE)   #_"WFE"   #_"1 0 1 1 1 1 1 1 0 0 1 0 0 0 0 0"
                    (= op code'WFI)   #_"WFI"   #_"1 0 1 1 1 1 1 1 0 0 1 1 0 0 0 0"
                    (= op code'YIELD) #_"YIELD" #_"1 0 1 1 1 1 1 1 0 0 0 1 0 0 0 0"
                )
                (do
                    (armv6m''update_pc this, pc)
                )
            )
        )
    )

    (defn #_"armv6m" armv6m''eval [#_"armv6m" this]
        (let [
            #_"u16" inst (armv6m''fetch this, (aget this i'pc))
        ]
            (or
                (armv6m''eval0 this, inst)
                (armv6m''eval1 this, inst)
                (armv6m''eval2 this, inst)
                (armv6m''eval3 this, inst)
                (armv6m''eval4 this, inst)
                (armv6m''eval5 this, inst)
                (armv6m''eval6 this, inst)
                (armv6m''eval7 this, inst)
                (armv6m''eval8 this, inst)
                (throw! "Not decoded")
            )
        )
    )

    (defn #_"cpu" cpu''step [#_"cpu" this]
        (let [
            this (armv6m''exc_return this)
        ]
            (armv6m''eval this)
        )
    )
)
