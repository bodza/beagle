(ns beagle.armv6m
    (:refer-clojure :only [* + - < << <= = >> >>> aget and aset bit-and bit-not bit-or bit-xor byte-array cons dec defmacro defn first if-not inc next not object-array or pos? when when-not zero?])
)

(defmacro § [& _])
(defmacro ß [& _])

(defmacro about [& s] (cons 'do s))

(about #_"armv6m"

    (def code'IGRP0 0) (def mask'IGRP0 0xf000)
    (def code'IGRP1 1) (def mask'IGRP1 0xf800)
    (def code'IGRP2 2) (def mask'IGRP2 0xfe00)
    (def code'IGRP3 3) (def mask'IGRP3 0xff00)
    (def code'IGRP4 4) (def mask'IGRP4 0xff80)
    (def code'IGRP5 5) (def mask'IGRP5 0xffc0)
    (def code'IGRP6 6) (def mask'IGRP6 0xffe0)
    (def code'IGRP7 7) (def mask'IGRP7 0xfff0)
    (def code'IGRP8 8) (def mask'IGRP8 0xffff)

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
    (def code'LDR    0x6800) (def mask'LDR    0xf800) #_"LDR <Rt>, [<Rn>{,#<imm5>}]"
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
    (def code'STR    0x6000) (def mask'STR    0xf800) #_"STR <Rt>, [<Rn>{,#<imm5>}]"
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
        (ram''write8 this, (+ addr 0), (>>> data 0))
        (ram''write8 this, (+ addr 1), (>>> data 8))
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
                (<< (§ cast #_"u32" (ram''read8 this, (+ addr 0))) 0)
                (<< (§ cast #_"u32" (ram''read8 this, (+ addr 1))) 8)
                (<< (§ cast #_"u32" (ram''read8 this, (+ addr 2))) 16)
                (<< (§ cast #_"u32" (ram''read8 this, (+ addr 3))) 24)
            )
        )
    )
)

(about #_"cpu"

    (def reg'SP    13)
    (def reg'LR    14)
    (def reg'PC    15)
    (def REGISTERS 16)

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

    (def i'ram         0) #_"ram"

    (def i'regfile     1) #_"[u32]"
    (def i'psp         2) #_"u32"
    (def i'msp         3) #_"u32"
    (def i'apsr        4) #_"u32"
    (def i'ipsr        5) #_"u32"
    (def i'epsr        6) #_"u32"

    (def i'primask     7) #_"u32"
    (def i'control     8) #_"u32"

    (def i'handler?    9) #_"bool"

    (def i'inst_group 10) #_"s32"
    (def i'rd         11) #_"u32"
    (def i'rt         12) #_"u32"
    (def i'rm         13) #_"u32"
    (def i'rn         14) #_"u32"
    (def i'imm        15) #_"u32"
    (def i'cond       16) #_"u32"
    (def i'reglist    17) #_"u32"

    (def size'cpu     18)

    (defn #_"cpu" cpu'new [#_"ram" ram]
        (let [
            #_"cpu" this (object-array size'cpu)
        ]
            (aset this i'ram ram)
            (let [
                #_"[u32]" regfile (object-array REGISTERS)
            ]
                (aset this i'regfile regfile)

                ;; Fetch SP and boot PC from vector table
                (aset regfile reg'SP    (cpu''read32 this,    (ram'base ram)))
                (aset regfile reg'PC (bit-and (cpu''read32 this, (+ (ram'base ram) 4)) (bit-not 1)))

                ;; Start in thread mode with main stack selected
                (aset this i'msp (aget regfile reg'SP))

                this
            )
        )
    )

    (defn #_"void" cpu''write8  [#_"cpu" this, #_"u32" addr, #_"u8"  data] (ram''write8  (aget this i'ram),    addr,              data) nil)
    (defn #_"void" cpu''write16 [#_"cpu" this, #_"u32" addr, #_"u16" data] (ram''write16 (aget this i'ram), (bit-and addr (bit-not 1)), data) nil)
    (defn #_"void" cpu''write32 [#_"cpu" this, #_"u32" addr, #_"u32" data] (ram''write32 (aget this i'ram), (bit-and addr (bit-not 3)), data) nil)

    (defn #_"u8"  cpu''read8  [#_"cpu" this, #_"u32" addr] (ram''read8  (aget this i'ram),    addr))
    (defn #_"u16" cpu''read16 [#_"cpu" this, #_"u32" addr] (ram''read16 (aget this i'ram), (bit-and addr (bit-not 1))))
    (defn #_"u32" cpu''read32 [#_"cpu" this, #_"u32" addr] (ram''read32 (aget this i'ram), (bit-and addr (bit-not 3))))

    (defn #_"cpu" cpu''step [#_"cpu" this]
        (let [
            #_"[u32]" regfile (aget this i'regfile)
        ]
            (when (= (bit-and (aget regfile reg'PC) EXC_RETURN) EXC_RETURN)
                (armv6m_exc_return this, (aget regfile reg'PC))
            )
            (let [
                #_"u16" inst                                 (armv6m_read_inst this,    (aget regfile reg'PC))
                #_"u16" inst2 (if (armv6m_decode this, inst) (armv6m_read_inst this, (+ (aget regfile reg'PC) 2)) 0)
            ]
                (armv6m_execute this, inst, inst2)
                this
            )
        )
    )

    (defn #_"u16" armv6m_read_inst [#_"cpu" this, #_"u32" addr]
        (if (zero? (bit-and addr 0x2))
            (bit-and (>>> (cpu''read32 this, addr)  0) 0xffff)
            (bit-and (>>> (cpu''read32 this, addr) 16) 0xffff)
        )
    )

    (defn #_"void" armv6m_update_sp [#_"cpu" this, #_"u32" sp]
        (aset (aget this i'regfile) reg'SP sp)

        (if (or (zero? (bit-and (aget this i'control) CONTROL_SPSEL)) (aget this i'handler?))
            (aset this i'msp sp)
            (aset this i'psp sp)
        )
        nil
    )

    (defn #_"void" armv6m_update_n_z_flags [#_"cpu" this, #_"u32" rd]
        ;; Zero
        (if (zero? rd)
            (aset this i'apsr (bit-or (aget this i'apsr)          flag'Z))
            (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'Z)))
        )

        ;; Negative
        (if-not (zero? (bit-and rd 0x80000000))
            (aset this i'apsr (bit-or (aget this i'apsr)          flag'N))
            (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'N)))
        )
        nil
    )

    (defn #_"u32" armv6m_add_with_carry [#_"cpu" this, #_"u32" rn, #_"u32" rm, #_"u32" carry_in, #_"u32" mask]
        (§ ass #_"u32" res (+ rn rm carry_in))

        ;; Zero
        (when-not (zero? (bit-and mask flag'Z))
            (if (zero? (bit-and res 0xffffffff))
                (aset this i'apsr (bit-or (aget this i'apsr)          flag'Z))
                (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'Z)))
            )
        )

        ;; Negative
        (when-not (zero? (bit-and mask flag'N))
            (if-not (zero? (bit-and res 0x80000000))
                (aset this i'apsr (bit-or (aget this i'apsr)          flag'N))
                (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'N)))
            )
        )

        ;; Carry
        (when-not (zero? (bit-and mask flag'C))
            (§ ass #_"u64" unsigned_sum (+ (§ cast #_"u64" rn) (§ cast #_"u64" rm) carry_in))
            (if (= unsigned_sum (§ cast #_"u64" res))
                (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'C)))
                (aset this i'apsr (bit-or (aget this i'apsr)          flag'C))
            )
        )

        ;; Overflow
        (when-not (zero? (bit-and mask flag'V))
            (§ ass #_"s64" signed_sum (+ (§ cast #_"s64" (§ cast #_"s32" rn)) (§ cast #_"s64" (§ cast #_"s32" rm)) carry_in))
            (if (= signed_sum (§ cast #_"s64" (§ cast #_"s32" res)))
                (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'V)))
                (aset this i'apsr (bit-or (aget this i'apsr)          flag'V))
            )
        )

        (§ cast #_"u32" res)
    )

    (defn #_"u32" armv6m_shift_left [#_"cpu" this, #_"u32" val, #_"u32" shift, #_"u32" mask]
        (§ ass #_"u64" res val)
        (§ ass res (<< res shift))

        ;; Carry Out (res[32])
        (when-not (zero? (bit-and mask flag'C))
            (if-not (zero? (bit-and res (<< (§ cast #_"u64" 1) 32)))
                (aset this i'apsr (bit-or (aget this i'apsr)          flag'C))
                (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'C)))
            )
        )

        ;; Zero
        (if (zero? (bit-and res 0xffffffff))
            (aset this i'apsr (bit-or (aget this i'apsr)          flag'Z))
            (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'Z)))
        )

        ;; Negative
        (if-not (zero? (bit-and res 0x80000000))
            (aset this i'apsr (bit-or (aget this i'apsr)          flag'N))
            (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'N)))
        )

        (§ cast #_"u32" res)
    )

    (defn #_"u32" armv6m_shift_right [#_"cpu" this, #_"u32" val, #_"u32" shift, #_"u32" mask]
        (§ ass #_"u32" res (if (< shift 32) val 0))

        ;; Carry Out (val[shift-1])
        (when (and (not (zero? (bit-and mask flag'C))) (pos? shift))
            ;; Last lost bit shifted right
            (if (and (not (zero? (bit-and val (<< 1 (dec shift))))) (<= shift 32))
                (aset this i'apsr (bit-or (aget this i'apsr)          flag'C))
                (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'C)))
            )
        )

        (§ ass res (>>> res shift))

        ;; Zero
        (if (zero? (bit-and res 0xffffffff))
            (aset this i'apsr (bit-or (aget this i'apsr)          flag'Z))
            (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'Z)))
        )

        ;; Negative
        (if-not (zero? (bit-and res 0x80000000))
            (aset this i'apsr (bit-or (aget this i'apsr)          flag'N))
            (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'N)))
        )

        res
    )

    (defn #_"u32" armv6m_arith_shift_right [#_"cpu" this, #_"u32" val, #_"u32" shift, #_"u32" mask]
        (§ ass #_"s32" res val)

        ;; Carry Out (val[shift-1])
        (when (and (not (zero? (bit-and mask flag'C))) (pos? shift))
            ;; Last lost bit shifted right
            (if-not (zero? (bit-and val (<< 1 (dec shift))))
                (aset this i'apsr (bit-or (aget this i'apsr)          flag'C))
                (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'C)))
            )
        )

        (§ ass res (>> res shift))

        ;; Zero
        (if (zero? (bit-and res 0xffffffff))
            (aset this i'apsr (bit-or (aget this i'apsr)          flag'Z))
            (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'Z)))
        )

        ;; Negative
        (if-not (zero? (bit-and res 0x80000000))
            (aset this i'apsr (bit-or (aget this i'apsr)          flag'N))
            (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'N)))
        )

        res
    )

    (defn #_"u32" armv6m_rotate_right [#_"cpu" this, #_"u32" val, #_"u32" shift, #_"u32" mask]
        (§ ass #_"u32" res)

        (if (zero? shift)
            (§ ass res val)
            (do
                (§ ass shift (bit-and shift 0x1f))

                (§ ass res (>>> val shift))
                (§ ass res (bit-or res (<< val (- 32 shift))))
            )
        )

        ;; Carry out
        (if-not (zero? (bit-and res 0x80000000))
            (aset this i'apsr (bit-or (aget this i'apsr)          flag'C))
            (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'C)))
        )

        ;; Zero
        (if (zero? (bit-and res 0xffffffff))
            (aset this i'apsr (bit-or (aget this i'apsr)          flag'Z))
            (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'Z)))
        )

        ;; Negative
        (if-not (zero? (bit-and res 0x80000000))
            (aset this i'apsr (bit-or (aget this i'apsr)          flag'N))
            (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'N)))
        )

        res
    )

    (defn #_"u32" armv6m_sign_extend [#_"cpu" this, #_"u32" val, #_"s32" offset]
        (if-not (zero? (bit-and val (<< 1 (dec offset))))
            (bit-or  val          (<< (bit-not 0) offset))
            (bit-and val (bit-not (<< (bit-not 0) offset)))
        )
    )

    (defn #_"u32" armv6m_exception [#_"cpu" this, #_"u32" pc, #_"u32" exception]
        (§ ass #_"u32" sp)

        ;; Retrieve shadow stack pointer (depending on mode)
        (if (or (zero? (bit-and (aget this i'control) CONTROL_SPSEL)) (aget this i'handler?))
            (§ ass sp (aget this i'msp))
            (§ ass sp (aget this i'psp))
        )

        ;; Push frame onto current stack
        (§ ass sp (- sp 4))
        (cpu''write32 this, sp, (aget this i'apsr))
        (§ ass sp (- sp 4))
        (cpu''write32 this, sp, (aget (aget this i'regfile) reg'PC))
        (§ ass sp (- sp 4))
        (cpu''write32 this, sp, (aget (aget this i'regfile) reg'LR))
        (§ ass sp (- sp 4))
        (cpu''write32 this, sp, (aget (aget this i'regfile) 12))
        (§ ass sp (- sp 4))
        (cpu''write32 this, sp, (aget (aget this i'regfile) 3))
        (§ ass sp (- sp 4))
        (cpu''write32 this, sp, (aget (aget this i'regfile) 2))
        (§ ass sp (- sp 4))
        (cpu''write32 this, sp, (aget (aget this i'regfile) 1))
        (§ ass sp (- sp 4))
        (cpu''write32 this, sp, (aget (aget this i'regfile) 0))
        (aset (aget this i'regfile) reg'SP sp)

        ;; Record exception
        (aset this i'ipsr (bit-and exception 0x3f))

        ;; Fetch exception vector address into PC
        (aset (aget this i'regfile) reg'PC (bit-and (cpu''read32 this, (+ (ram'base (aget this i'ram)) (* exception 4))) (bit-not 1)))

        (if (aget this i'handler?)
            (do
                ;; LR = Return to handler mode (recursive interrupt?)
                (aset (aget this i'regfile) reg'LR 0xfffffff1)
            )
            (if (zero? (bit-and (aget this i'control) CONTROL_SPSEL))
                (do
                    ;; LR = Return to thread mode (with main stack)
                    (aset (aget this i'regfile) reg'LR 0xfffffff9)
                )
                (do
                    ;; LR = Return to thread mode (with process stack)
                    (aset (aget this i'regfile) reg'LR 0xfffffffd)
                )
            )
        )

        ;; Swap to handler mode
        (aset this i'handler? true)

        ;; Current stack is now main
        (aset this i'control (bit-and (aget this i'control) (bit-not CONTROL_SPSEL)))

        (aget (aget this i'regfile) reg'PC)
    )

    (defn #_"void" armv6m_exc_return [#_"cpu" this, #_"u32" pc]
        (when (and (aget this i'handler?) (= (bit-and pc EXC_RETURN) EXC_RETURN))
            ;; TODO: Should be 0x1f...
            (§ switch (bit-and pc 0xf)
                (§ case 0x1)
                (§
                    (aset this i'handler? true)
                    (aset this i'control (bit-and (aget this i'control) (bit-not CONTROL_SPSEL)))
                    (§ break)
                )
                (§ case 0x9)
                (§
                    (aset this i'handler? false)
                    (aset this i'control (bit-and (aget this i'control) (bit-not CONTROL_SPSEL)))
                    (§ break)
                )
                (§ case 0xd)
                (§
                    (aset this i'handler? false)
                    (aset this i'control (bit-or (aget this i'control) CONTROL_SPSEL))
                    (§ break)
                )
                (§ default)
                (§
                    (§ throw "Not handled")
                    (§ break)
                )
            )

            (§ ass #_"u32" sp (aget (aget this i'regfile) reg'SP))
            (aset (aget this i'regfile) 0 (cpu''read32 this, sp))
            (§ ass sp (+ sp 4))
            (aset (aget this i'regfile) 1 (cpu''read32 this, sp))
            (§ ass sp (+ sp 4))
            (aset (aget this i'regfile) 2 (cpu''read32 this, sp))
            (§ ass sp (+ sp 4))
            (aset (aget this i'regfile) 3 (cpu''read32 this, sp))
            (§ ass sp (+ sp 4))
            (aset (aget this i'regfile) 12 (cpu''read32 this, sp))
            (§ ass sp (+ sp 4))
            (aset (aget this i'regfile) reg'LR (cpu''read32 this, sp))
            (§ ass sp (+ sp 4))
            (aset (aget this i'regfile) reg'PC (cpu''read32 this, sp))
            (§ ass sp (+ sp 4))
            (aset this i'apsr (cpu''read32 this, sp))
            (§ ass sp (+ sp 4))
            (armv6m_update_sp this, sp)
        )
        nil
    )

    (defn #_"bool" armv6m_decode [#_"cpu" this, #_"u16" inst]
        (§ ass #_"bool" res false)
        (§ ass #_"bool" decoded? false)

        (aset this i'rd 0)
        (aset this i'rt 0)
        (aset this i'rm 0)
        (aset this i'rn 0)
        (aset this i'imm 0)
        (aset this i'cond 0)
        (aset this i'reglist 0)

        ;; Group 0?
        (when-not decoded?
            (§ ass decoded? true)
            (aset this i'inst_group code'IGRP0)
            (§ switch (bit-and inst mask'IGRP0)
                #_"BCC <label>"
                #_"1 1 0 1 cond imm8"
                (§ case code'BCC)
                (§
                    (aset this i'cond (bit-and (>>> inst 8) 0x0f))
                    (aset this i'imm (bit-and (>>> inst 0) 0xff))
                    (§ break)
                )
                (§ default)
                (§
                    (§ ass decoded? false)
                    (§ break)
                )
            )
        )

        ;; Group 1?
        (when-not decoded?
            (§ ass decoded? true)
            (aset this i'inst_group code'IGRP1)
            (§ switch (bit-and inst mask'IGRP1)
                #_"ADDS <Rdn>,#<imm8>"
                #_"0 0 1 1 0 Rdn imm8"
                (§ case code'ADDS_1)
                #_"SUBS <Rdn>,#<imm8>"
                #_"0 0 1 11 Rdn imm8"
                (§ case code'SUBS_1)
                (§
                    (aset this i'rd (bit-and (>>> inst 8) 0x7))
                    (aset this i'rn (aget this i'rd))
                    (aset this i'imm (bit-and (>>> inst 0) 0xff))
                    (§ break)
                )

                #_"ADR <Rd>,<label>"
                #_"1 0 1 0 0 Rd imm8"
                (§ case code'ADR)
                #_"MOVS <Rd>,#<imm8>"
                #_"0 0 1 0 0 Rd imm8"
                (§ case code'MOVS)
                (§
                    (aset this i'rd (bit-and (>>> inst 8) 0x7))
                    (aset this i'imm (bit-and (>>> inst 0) 0xff))
                    (§ break)
                )

                #_"ASRS <Rd>,<Rm>,#<imm5>"
                #_"0 0 0 1 0 imm5 Rm Rd"
                (§ case code'ASRS)
                #_"LSLS <Rd>,<Rm>,#<imm5>"
                #_"0 0 0 0 0 imm5 Rm Rd"
                (§ case code'LSLS)
                #_"LSRS <Rd>,<Rm>,#<imm5>"
                #_"0 0 0 0 1 imm5 Rm Rd"
                (§ case code'LSRS)
                (§
                    (aset this i'imm (bit-and (>>> inst 6) 0x1f))
                    (aset this i'rm (bit-and (>>> inst 3) 0x7))
                    (aset this i'rd (bit-and (>>> inst 0) 0x7))
                    (§ break)
                )

                #_"B <label>"
                #_"1 1 1 0 0 imm11"
                (§ case code'B)
                (§
                    (aset this i'imm (bit-and (>>> inst 0) 0x7ff))
                    (§ break)
                )

                #_"BL <label>"
                #_"1 1 1 01 S imm10 1 1 J1 1 J2 imm11"
                (§ case code'BL)
                (§
                    ;; 32-bit instruction
                    (§ ass res true)
                    (aset this i'imm (bit-and (>>> inst 0) 0x7ff))
                    (aset this i'rd reg'LR)

                    ;; TODO: Clean this up
                    ;; Check next instruction to work out if this is a BL or MSR
                    (when-not (= (bit-and (armv6m_read_inst this, (+ (aget (aget this i'regfile) reg'PC) 2)) 0xc000) 0xc000)
                        (§ ass decoded? false)
                    )
                    (§ break)
                )

                #_"CMP <Rn>,#<imm8>"
                #_"0 0 1 0 1 Rn imm8"
                (§ case code'CMP)
                (§
                    (aset this i'rn (bit-and (>>> inst 8) 0x7))
                    (aset this i'imm (bit-and (>>> inst 0) 0xff))
                    (§ break)
                )

                #_"LDM <Rn>!,<registers> <Rn> not included in <registers>"
                #_"1 1 0 0 1 Rn register_list"
                #_"LDM <Rn>,<registers> <Rn> included in <registers>"
                #_"1 1 0 0 1 Rn register_list"
             ;; (§ case code'LDM_1)
                (§ case code'LDM)
                #_"STM <Rn>!,<registers>"
                #_"1 1 0 0 0 Rn register_list"
                (§ case code'STM)
                (§
                    (aset this i'rn (bit-and (>>> inst 8) 0x7))
                    (aset this i'rd (aget this i'rn))
                    (aset this i'reglist (bit-and (>>> inst 0) 0xff))
                    (§ break)
                )

                #_"LDR <Rt>, [<Rn>{,#<imm5>}]"
                #_"0 1 1 0 1 imm5 Rn Rt"
                (§ case code'LDR)
                #_"LDRB <Rt>,[<Rn>{,#<imm5>}]"
                #_"0 1 1 1 1 imm5 Rn Rt"
                (§ case code'LDRB)
                #_"LDRH <Rt>,[<Rn>{,#<imm5>}]"
                #_"1 0 0 0 1 imm5 Rn Rt"
                (§ case code'LDRH)
                #_"STR <Rt>, [<Rn>{,#<imm5>}]"
                #_"0 1 1 0 0 imm5 Rn Rt"
                (§ case code'STR)
                #_"STRB <Rt>,[<Rn>,#<imm5>]"
                #_"0 1 1 1 0 imm5 Rn Rt"
                (§ case code'STRB)
                #_"STRH <Rt>,[<Rn>{,#<imm5>}]"
                #_"1 0 0 0 0 imm5 Rn Rt"
                (§ case code'STRH)
                (§
                    (aset this i'imm (bit-and (>>> inst 6) 0x1f))
                    (aset this i'rn (bit-and (>>> inst 3) 0x7))
                    (aset this i'rt (bit-and (>>> inst 0) 0x7))
                    (aset this i'rd (aget this i'rt))
                    (§ break)
                )

                #_"LDR <Rt>,<label>"
                #_"0 1 0 0 1 Rt imm8"
                (§ case code'LDR_2)
                (§
                    (aset this i'rt (bit-and (>>> inst 8) 0x7))
                    (aset this i'rd (aget this i'rt))
                    (aset this i'imm (bit-and (>>> inst 0) 0xff))
                    (§ break)
                )

                #_"LDR <Rt>,[SP{,#<imm8>}]"
                #_"1 0 0 1 1 Rt imm8"
                (§ case code'LDR_1)
                #_"STR <Rt>,[SP,#<imm8>]"
                #_"1 0 0 1 0 Rt imm8"
                (§ case code'STR_1)
                #_"ADD <Rd>,SP,#<imm8>"
                #_"1 0 1 0 1 Rd imm8"
                (§ case code'ADD_1)
                (§
                    (aset this i'rt (bit-and (>>> inst 8) 0x7))
                    (aset this i'rn reg'SP)
                    (aset this i'rd (aget this i'rt))
                    (aset this i'imm (bit-and (>>> inst 0) 0xff))
                    (§ break)
                )

                (§ default)
                (§
                    (§ ass decoded? false)
                    (§ break)
                )
            )
        )

        ;; Group 2?
        (when-not decoded?
            (§ ass decoded? true)
            (aset this i'inst_group code'IGRP2)
            (§ switch (bit-and inst mask'IGRP2)
                #_"ADDS <Rd>,<Rn>,#<imm3>"
                #_"0 0 0 1 1 1 0 imm3 Rn Rd"
                (§ case code'ADDS)
                #_"SUBS <Rd>,<Rn>,#<imm3>"
                #_"0 0 0 11 1 1 imm3 Rn Rd"
                (§ case code'SUBS)
                (§
                    (aset this i'imm (bit-and (>>> inst 6) 0x7))
                    (aset this i'rn (bit-and (>>> inst 3) 0x7))
                    (aset this i'rd (bit-and (>>> inst 0) 0x7))
                    (§ break)
                )

                #_"ADDS <Rd>,<Rn>,<Rm>"
                #_"0 0 0 1 1 0 0 Rm Rn Rd"
                (§ case code'ADDS_2)
                #_"SUBS <Rd>,<Rn>,<Rm>"
                #_"0 0 0 11 0 1 Rm Rn Rd"
                (§ case code'SUBS_2)
                (§
                    (aset this i'rm (bit-and (>>> inst 6) 0x7))
                    (aset this i'rn (bit-and (>>> inst 3) 0x7))
                    (aset this i'rd (bit-and (>>> inst 0) 0x7))
                    (§ break)
                )

                #_"LDR <Rt>,[<Rn>,<Rm>]"
                #_"0 1 0 1 1 0 0 Rm Rn Rt"
                (§ case code'LDR_3)
                #_"LDRB <Rt>,[<Rn>,<Rm>]"
                #_"0 1 0 1 1 1 0 Rm Rn Rt"
                (§ case code'LDRB_1)
                #_"LDRH <Rt>,[<Rn>,<Rm>]"
                #_"0 1 0 1 1 0 1 Rm Rn Rt"
                (§ case code'LDRH_1)
                #_"LDRSB <Rt>,[<Rn>,<Rm>]"
                #_"0 1 0 1 0 1 1 Rm Rn Rt"
                (§ case code'LDRSB)
                #_"LDRSH <Rt>,[<Rn>,<Rm>]"
                #_"0 1 0 1 1 1 1 Rm Rn Rt"
                (§ case code'LDRSH)
                #_"STR <Rt>,[<Rn>,<Rm>]"
                #_"0 1 0 1 0 00 Rm Rn Rt"
                (§ case code'STR_2)
                #_"STRB <Rt>,[<Rn>,<Rm>]"
                #_"0 1 0 1 0 1 0 Rm Rn Rt"
                (§ case code'STRB_1)
                #_"STRH <Rt>,[<Rn>,<Rm>]"
                #_"0 1 0 1 0 0 1 Rm Rn Rt"
                (§ case code'STRH_1)
                (§
                    (aset this i'rm (bit-and (>>> inst 6) 0x7))
                    (aset this i'rn (bit-and (>>> inst 3) 0x7))
                    (aset this i'rt (bit-and (>>> inst 0) 0x7))
                    (aset this i'rd (aget this i'rt))
                    (§ break)
                )

                #_"POP <registers>"
                #_"1 0 1 1 1 1 0 P register_list"
                (§ case code'POP)
                (§
                    (aset this i'reglist (bit-and (>>> inst 0) 0xff))
                    (when-not (zero? (bit-and inst (<< 1 8)))
                        (aset this i'reglist (bit-or (aget this i'reglist) (<< 1 reg'PC)))
                    )
                    (§ break)
                )

                #_"PUSH <registers>"
                #_"1 0 1 1 0 1 0 M register_list"
                (§ case code'PUSH)
                (§
                    (aset this i'reglist (bit-and (>>> inst 0) 0xff))
                    (when-not (zero? (bit-and inst (<< 1 8)))
                        (aset this i'reglist (bit-or (aget this i'reglist) (<< 1 reg'LR)))
                    )
                    (§ break)
                )

                (§ default)
                (§
                    (§ ass decoded? false)
                    (§ break)
                )
            )
        )

        ;; Group 3?
        (when-not decoded?
            (§ ass decoded? true)
            (aset this i'inst_group code'IGRP3)
            (§ switch (bit-and inst mask'IGRP3)
                #_"ADD <Rdn>,<Rm>"
                #_"0 1 0 0 0 1 0 0 Rm Rdn"
                (§ case code'ADD)
                (§
                    (aset this i'rm (bit-and (>>> inst 3) 0xf))
                    (aset this i'rd (bit-and (>>> inst 0) 0x7))
                    (aset this i'rd (bit-or (aget this i'rd) (bit-and (>>> inst 4) 0x8)))
                    (aset this i'rn (aget this i'rd))
                    (§ break)
                )

                #_"BKPT #<imm8>"
                #_"1 0 1 1 1 1 1 0 imm8"
                (§ case code'BKPT)
                #_"SVC #<imm8>"
                #_"1 1 0 1 111 1 imm8"
                (§ case code'SVC)
                #_"UDF #<imm8>"
                #_"1 1 0 1 1 1 1 0 imm8"
                (§ case code'UDF)
                (§
                    (aset this i'imm (bit-and (>>> inst 0) 0xff))
                    (§ break)
                )

                #_"CMP <Rn>,<Rm> <Rn> and <Rm> not both from R0-R7"
                #_"0 1 0 0 0 1 0 1 N Rm Rn"
                (§ case code'CMP_2)
                (§
                    (aset this i'rm (bit-and (>>> inst 3) 0xf))
                    (aset this i'rn (bit-and (>>> inst 0) 0x7))
                    (aset this i'rn (bit-or (aget this i'rn) (bit-and (>>> inst 4) 0x8)))
                    (§ break)
                )

                #_"MOV <Rd>,<Rm> Otherwise all versions of the Thumb instruction set."
                #_"0 1 0 0 0 1 1 0 D Rm Rd"
                (§ case code'MOV)
                (§
                    (aset this i'rm (bit-and (>>> inst 3) 0xf))
                    (aset this i'rd (bit-and (>>> inst 0) 0x7))
                    (aset this i'rd (bit-or (aget this i'rd) (bit-and (>>> inst 4) 0x8)))
                    (§ break)
                )

                (§ default)
                (§
                    (§ ass decoded? false)
                    (§ break)
                )
            )
        )

        ;; Group 4?
        (when-not decoded?
            (§ ass decoded? true)
            (aset this i'inst_group code'IGRP4)
            (§ switch (bit-and inst mask'IGRP4)
                #_"ADD SP,SP,#<imm7>"
                #_"1 0 1 1 0 0 0 0 0 imm7"
                (§ case code'ADD_2)
                #_"SUB SP,SP,#<imm7>"
                #_"1 0 1 1 000 0 1 imm7"
                (§ case code'SUB)
                (§
                    (aset this i'rn reg'SP)
                    (aset this i'rd reg'SP)
                    (aset this i'imm (bit-and (>>> inst 0) 0x7f))
                    (§ break)
                )

                #_"BLX <Rm>"
                #_"0 1 0 0 0 1 1 1 1 Rm (0) (0) (0)"
                (§ case code'BLX)
                (§
                    (aset this i'rm (bit-and (>>> inst 3) 0xf))
                    (aset this i'rd reg'LR)
                    (§ break)
                )

                #_"BX <Rm>"
                #_"0 1 0 0 0 1 1 1 0 Rm (0) (0) (0)"
                (§ case code'BX)
                (§
                    (aset this i'rm (bit-and (>>> inst 3) 0xf))
                    (§ break)
                )

                (§ default)
                (§
                    (§ ass decoded? false)
                    (§ break)
                )
            )
        )

        ;; Group 5?
        (when-not decoded?
            (§ ass decoded? true)
            (aset this i'inst_group code'IGRP5)
            (§ switch (bit-and inst mask'IGRP5)
                #_"ADCS <Rdn>,<Rm>"
                #_"0 1 0 0 0 0 0 1 0 1 Rm Rdn"
                (§ case code'ADCS)
                #_"ANDS <Rdn>,<Rm>"
                #_"0 1 0 0 0 0 0 0 0 0 Rm Rdn"
                (§ case code'ANDS)
                #_"ASRS <Rdn>,<Rm>"
                #_"0 1 0 0 0 0 0 1 0 0 Rm Rdn"
                (§ case code'ASRS_1)
                #_"BICS <Rdn>,<Rm>"
                #_"0 1 0 0 0 0 1 1 1 0 Rm Rdn"
                (§ case code'BICS)
                #_"EORS <Rdn>,<Rm>"
                #_"0 1 0 0 0 0 0 0 0 1 Rm Rdn"
                (§ case code'EORS)
                #_"LSLS <Rdn>,<Rm>"
                #_"0 1 0 0 0 0 0 0 1 0 Rm Rdn"
                (§ case code'LSLS_1)
                #_"LSRS <Rdn>,<Rm>"
                #_"0 1 0 0 0 0 0 0 1 1 Rm Rdn"
                (§ case code'LSRS_1)
                #_"ORRS <Rdn>,<Rm>"
                #_"0 1 0 0 0 0 1 1 0 0 Rm Rdn"
                (§ case code'ORRS)
                #_"RORS <Rdn>,<Rm>"
                #_"0 1 0 0 0 0 0 1 1 1 Rm Rdn"
                (§ case code'RORS)
                #_"SBCS <Rdn>,<Rm>"
                #_"0 1 0 0 0 0 0 1 1 0 Rm Rdn"
                (§ case code'SBCS)
                (§
                    (aset this i'rm (bit-and (>>> inst 3) 0x7))
                    (aset this i'rd (bit-and (>>> inst 0) 0x7))
                    (aset this i'rn (aget this i'rd))
                    (§ break)
                )

                #_"CMN <Rn>,<Rm>"
                #_"0 1 0 0 0 0 1 0 1 1 Rm Rn"
                (§ case code'CMN)
                #_"CMP <Rn>,<Rm> <Rn> and <Rm> both from R0-R7"
                #_"0 1 0 0 0 0 1 0 1 0 Rm Rn"
                (§ case code'CMP_1)
                #_"TST <Rn>,<Rm>"
                #_"000 1 0 0 1 0 0 0 Rm Rn"
                (§ case code'TST)
                (§
                    (aset this i'rm (bit-and (>>> inst 3) 0x7))
                    (aset this i'rn (bit-and (>>> inst 0) 0x7))
                    (§ break)
                )

                #_"MULS <Rdm>,<Rn>,<Rdm>"
                #_"0 1 0 0 0 0 1 1 0 1 Rn Rdm"
                (§ case code'MULS)
                (§
                    (aset this i'rn (bit-and (>>> inst 3) 0x7))
                    (aset this i'rd (bit-and (>>> inst 0) 0x7))
                    (aset this i'rm (aget this i'rd))
                    (§ break)
                )

                #_"MVNS <Rd>,<Rm>"
                #_"0 1 0 0 0 0 1 1 1 1 Rm Rd"
                (§ case code'MVNS)
                #_"REV <Rd>,<Rm>"
                #_"1 0 1 1 1 0 1 0 0 0 Rm Rd"
                (§ case code'REV)
                #_"REV16 <Rd>,<Rm>"
                #_"1 0 1 1 1 0 1 0 0 1 Rm Rd"
                (§ case code'REV16)
                #_"REVSH <Rd>,<Rm>"
                #_"1 0 1 1 1 0 1 0 1 1 Rm Rd"
                (§ case code'REVSH)
                #_"SXTB <Rd>,<Rm>"
                #_"1 0 1 1 100 0 0 1 Rm Rd"
                (§ case code'SXTB)
                #_"SXTH <Rd>,<Rm>"
                #_"1 0 1 1 100 0 0 0 Rm Rd"
                (§ case code'SXTH)
                #_"UXTB <Rd>,<Rm>"
                #_"1 0 1 1 100 0 1 1 Rm Rd"
                (§ case code'UXTB)
                #_"UXTH <Rd>,<Rm>"
                #_"1 0 1 1 100 0 1 0 Rm Rd"
                (§ case code'UXTH)
                (§
                    (aset this i'rm (bit-and (>>> inst 3) 0x7))
                    (aset this i'rd (bit-and (>>> inst 0) 0x7))
                    (§ break)
                )

                #_"RSBS <Rd>,<Rn>,#0"
                #_"0 1 0 0 0 0 1 0 0 1 Rn Rd"
                (§ case code'RSBS)
                (§
                    (aset this i'rn (bit-and (>>> inst 3) 0x7))
                    (aset this i'rd (bit-and (>>> inst 0) 0x7))
                    (§ break)
                )

                (§ default)
                (§
                    (§ ass decoded? false)
                    (§ break)
                )
            )
        )

        ;; Group 6?
        (when-not decoded?
            (§ ass decoded? true)
            (aset this i'inst_group code'IGRP6)
            (§ switch (bit-and inst mask'IGRP6)
                #_"MRS <Rd>,<spec_reg>"
                #_"1 1 1 01 0 1 1 1 1 1 (0) (1) (1) (1) (1) 1 0 (0) 0 Rd SYSm"
                (§ case code'MRS)
                (§
                    ;; 32-bit instruction
                    (§ ass res true)
                    (§ break)
                )
                #_"MSR <spec_reg>,<Rn>"
                #_"1 1 1 01 0 1 1 1 0 0 (0) Rn 1 0 (0) 0 (1) (0) (0) (0) SYSm"
                (§ case code'MSR)
                (§
                    (aset this i'rn (bit-and (>>> inst 0) 0xf))

                    ;; 32-bit instruction
                    (§ ass res true)
                    (§ break)
                )
                #_"CPS<effect> i"
                #_"1 0 1 1 0 1 1 0 0 1 1 im (0) (0) (1) (0)"
                (§ case code'CPS)
                (§
                    (aset this i'imm (bit-and (>>> inst 4) 0x1))
                    (§ break)
                )

                (§ default)
                (§
                    (§ ass decoded? false)
                    (§ break)
                )
            )
        )

        ;; Group 7?
        (when-not decoded?
            (§ ass decoded? true)
            (aset this i'inst_group code'IGRP7)
            (§ switch (bit-and inst mask'IGRP7)
                #_"DMB #<option>"
                #_"1 1 1 01 0 1 1 1 0 1 1 (1) (1) (1) (1) 1 0 (0) 0 (1) (1) (1) (1) 0 1 0 1 option"
             ;; (§ case code'DMB)
                #_"DSB #<option>"
                #_"1 1 1 01 0 1 1 1 0 1 1 (1) (1) (1) (1) 1 0 (0) 0 (1) (1) (1) (1) 0 1 0 0 option"
             ;; (§ case code'DSB)
                #_"ISB #<option>"
                #_"1 1 1 01 0 1 1 1 0 1 1 (1) (1) (1) (1) 1 0 (0) 0 (1) (1) (1) (1) 0 1 1 0 option"
                (§ case code'ISB)
                (§
                    ;; 32-bit instruction
                    (§ ass res true)

                    ;; Do nothing
                    (§ break)
                )
                #_"UDF_W #<imm16>"
                #_"1 11 1 0 1 1 1 1 1 1 1 imm4 1 0 1 0 imm12"
                (§ case code'UDF_W)
                (§
                    ;; 32-bit instruction
                    (§ ass res true)

                    ;; Do nothing
                    (§ break)
                )

                (§ default)
                (§
                    (§ ass decoded? false)
                    (§ break)
                )
            )
        )

        ;; Group 8?
        (when-not decoded?
            (§ ass decoded? true)
            (aset this i'inst_group code'IGRP8)
            (§ switch (bit-and inst mask'IGRP8)
                #_"NOP"
                #_"1 0 1 1 1 1 1 1 0 0 0 0 0 0 0 0"
                (§ case code'NOP)
                (§
                    ;; Do nothing
                    (§ break)
                )
                #_"SEV"
                #_"1 0 1 1 1 1 1 1 0 1 0 0 0 0 0 0"
                (§ case code'SEV)
                (§
                    ;; Do nothing
                    (§ break)
                )
                #_"WFE"
                #_"1 0 1 1 1 1 1 1 0 0 1 0 0 0 0 0"
                (§ case code'WFE)
                (§
                    ;; Do nothing
                    (§ break)
                )
                #_"WFI"
                #_"1 0 1 1 1 1 1 1 0 0 1 1 0 0 0 0"
                (§ case code'WFI)
                (§
                    ;; Do nothing
                    (§ break)
                )
                #_"YIELD"
                #_"1 0 1 1 1 1 1 1 0 0 0 1 0 0 0 0"
                (§ case code'YIELD)
                (§
                    ;; Do nothing
                    (§ break)
                )

                (§ default)
                (§
                    (§ ass decoded? false)
                    (§ break)
                )
            )
        )

        (when-not decoded?
            (§ throw "Instruction decode failed")
        )

        res
    )

    (defn #_"void" armv6m_execute [#_"cpu" this, #_"u16" inst, #_"u16" inst2]
        (§ ass #_"u32" reg_rm (aget (aget this i'regfile) (aget this i'rm)))
        (§ ass #_"u32" reg_rn (aget (aget this i'regfile) (aget this i'rn)))
        (§ ass #_"u32" reg_rd 0)
        (§ ass #_"u32" pc (aget (aget this i'regfile) reg'PC))
        (§ ass #_"u32" offset 0)
        (§ ass #_"bool" write_rd false)

        (§ ass pc (+ pc 2))

        (§ switch ((aget this i'inst_group))
            (§ case code'IGRP0)
            (§
                (§ switch (bit-and inst mask'IGRP0)
                    #_"BCC <label>"
                    #_"1 1 0 1 cond imm8"
                    (§ case code'BCC)
                    (§
                        ;; Sign extend offset
                        (§ ass offset (armv6m_sign_extend this, (aget this i'imm), 8))

                        ;; Convert to words
                        (§ ass offset (<< offset 1))

                        ;; Make relative to PC + 4
                        (§ ass offset (+ offset pc 2))

                        (§ switch ((aget this i'cond))
                            (§ case 0) #_"EQ"
                            (§
                                (when-not (zero? (bit-and (aget this i'apsr) flag'Z))
                                    (§ ass pc offset)
                                )
                                (§ break)
                            )
                            (§ case 1) #_"NE"
                            (§
                                (when (zero? (bit-and (aget this i'apsr) flag'Z))
                                    (§ ass pc offset)
                                )
                                (§ break)
                            )
                            (§ case 2) #_"CS/HS"
                            (§
                                (when-not (zero? (bit-and (aget this i'apsr) flag'C))
                                    (§ ass pc offset)
                                )
                                (§ break)
                            )
                            (§ case 3) #_"CC/LO"
                            (§
                                (when (zero? (bit-and (aget this i'apsr) flag'C))
                                    (§ ass pc offset)
                                )
                                (§ break)
                            )
                            (§ case 4) #_"MI"
                            (§
                                (when-not (zero? (bit-and (aget this i'apsr) flag'N))
                                    (§ ass pc offset)
                                )
                                (§ break)
                            )
                            (§ case 5) #_"PL"
                            (§
                                (when (zero? (bit-and (aget this i'apsr) flag'N))
                                    (§ ass pc offset)
                                )
                                (§ break)
                            )
                            (§ case 6) #_"VS"
                            (§
                                (when-not (zero? (bit-and (aget this i'apsr) flag'V))
                                    (§ ass pc offset)
                                )
                                (§ break)
                            )
                            (§ case 7) #_"VC"
                            (§
                                (when (zero? (bit-and (aget this i'apsr) flag'V))
                                    (§ ass pc offset)
                                )
                                (§ break)
                            )
                            (§ case 8) #_"HI"
                            (§
                                (when (and (not (zero? (bit-and (aget this i'apsr) flag'C))) (zero? (bit-and (aget this i'apsr) flag'Z)))
                                    (§ ass pc offset)
                                )
                                (§ break)
                            )
                            (§ case 9) #_"LS"
                            (§
                                (when (or (zero? (bit-and (aget this i'apsr) flag'C)) (not (zero? (bit-and (aget this i'apsr) flag'Z))))
                                    (§ ass pc offset)
                                )
                                (§ break)
                            )
                            (§ case 10) #_"GE"
                            (§
                                (when (= (>>> (bit-and (aget this i'apsr) flag'N) shift'N) (>>> (bit-and (aget this i'apsr) flag'V) shift'V))
                                    (§ ass pc offset)
                                )
                                (§ break)
                            )
                            (§ case 11) #_"LT"
                            (§
                                (when-not (= (>>> (bit-and (aget this i'apsr) flag'N) shift'N) (>>> (bit-and (aget this i'apsr) flag'V) shift'V))
                                    (§ ass pc offset)
                                )
                                (§ break)
                            )
                            (§ case 12) #_"GT"
                            (§
                                (when (and (zero? (bit-and (aget this i'apsr) flag'Z)) (= (>>> (bit-and (aget this i'apsr) flag'N) shift'N) (>>> (bit-and (aget this i'apsr) flag'V) shift'V)))
                                    (§ ass pc offset)
                                )
                                (§ break)
                            )
                            (§ case 13) #_"LE"
                            (§
                                (when (or (not (zero? (bit-and (aget this i'apsr) flag'Z))) (not (= (>>> (bit-and (aget this i'apsr) flag'N) shift'N) (>>> (bit-and (aget this i'apsr) flag'V) shift'V))))
                                    (§ ass pc offset)
                                )
                                (§ break)
                            )
                            (§ case 14) #_"AL"
                            (§
                                (§ ass pc offset)
                                (§ break)
                            )
                            (§ case 15) #_"SVC"
                            (§
                                (§ ass pc (armv6m_exception this, pc, 11))
                                (§ break)
                            )
                            (§ default)
                            (§
                                (§ throw "Bad condition code")
                                (§ break)
                            )
                        )
                        (§ break)
                    )
                )
                (§ break)
            )
            (§ case code'IGRP1)
            (§
                (§ switch (bit-and inst mask'IGRP1)
                    #_"ADDS <Rdn>,#<imm8>"
                    #_"0 0 1 1 0 Rdn imm8"
                    (§ case code'ADDS_1)
                    (§
                        (§ ass reg_rd (armv6m_add_with_carry this, reg_rn, (aget this i'imm), 0, flags'all))
                        (§ ass write_rd true)
                        (§ break)
                    )
                    #_"ADD <Rd>,SP,#<imm8>"
                    #_"1 0 1 0 1 Rd imm8"
                    (§ case code'ADD_1)
                    (§
                        (§ ass reg_rd (+ reg_rn (<< (aget this i'imm) 2)))
                        (§ ass write_rd true)
                        (§ break)
                    )
                    #_"ADR <Rd>,<label>"
                    #_"1 0 1 0 0 Rd imm8"
                    (§ case code'ADR)
                    (§
                        (§ ass reg_rd (+ pc (aget this i'imm) 2))
                        (§ ass write_rd true)
                        (§ break)
                    )
                    #_"ASRS <Rd>,<Rm>,#<imm5>"
                    #_"0 0 0 1 0 imm5 Rm Rd"
                    (§ case code'ASRS)
                    (§
                        (when (zero? (aget this i'imm))
                            (aset this i'imm 32)
                        )

                        (§ ass reg_rd (armv6m_arith_shift_right this, reg_rm, (aget this i'imm), flags'NZC))
                        (§ ass write_rd true)
                        (§ break)
                    )
                    #_"B <label>"
                    #_"1 1 1 0 0 imm11"
                    (§ case code'B)
                    (§
                        ;; Sign extend offset
                        (§ ass offset (armv6m_sign_extend this, (aget this i'imm), 11))

                        ;; Convert to words
                        (§ ass offset (<< offset 1))

                        ;; Make relative to PC + 4
                        (§ ass offset (+ offset pc 2))

                        (§ ass pc offset)
                        (§ break)
                    )
                    #_"BL <label>"
                    #_"1 1 1 01 S imm10 1 1 J1 1 J2 imm11"
                    (§ case code'BL)
                    (§
                        ;; Sign extend
                        (§ ass offset (armv6m_sign_extend this, (aget this i'imm), 11))
                        (§ ass offset (<< offset 11))

                        ;; Additional range
                        (aset this i'imm (bit-and (>>> inst2 0) 0x7ff))
                        (§ ass offset (bit-or offset (aget this i'imm)))

                        ;; Make relative to PC
                        (§ ass offset (<< offset 1))
                        (§ ass offset (+ offset pc))

                     ;; (aset this i'rd reg'LR)
                        (§ ass reg_rd (bit-or (+ pc 2) 1))
                        (§ ass write_rd true)

                        (§ ass pc (+ offset 2))
                        (§ break)
                    )
                    #_"CMP <Rn>,#<imm8>"
                    #_"0 0 1 0 1 Rn imm8"
                    (§ case code'CMP)
                    (§
                        (§ ass reg_rd (armv6m_add_with_carry this, reg_rn, (bit-not (aget this i'imm)), 1, flags'all))
                        ;; No writeback
                        (§ break)
                    )
                    #_"LDM <Rn>!,<registers> <Rn> not included in <registers>"
                    #_"1 1 0 0 1 Rn register_list"
                    #_"LDM <Rn>,<registers> <Rn> included in <registers>"
                    #_"1 1 0 0 1 Rn register_list"
                 ;; (§ case code'LDM_1)
                    (§ case code'LDM)
                    (§
                        (§ for (§ ass #_"s32" i 0) (and (< i REGISTERS) (not (zero? (aget this i'reglist)))) (§ ass i (inc i))
                            (when-not (zero? (bit-and (aget this i'reglist) (<< 1 i)))
                                (aset (aget this i'regfile) i (cpu''read32 this, reg_rn))
                                (when (= i reg'PC)
                                    (when-not (= (bit-and (aget (aget this i'regfile) i) EXC_RETURN) EXC_RETURN)
                                        (aset (aget this i'regfile) i (bit-and (aget (aget this i'regfile) i) (bit-not 1)))
                                    )
                                    (§ ass pc (aget (aget this i'regfile) i))
                                )
                                (§ ass reg_rn (+ reg_rn 4))
                                (aset this i'reglist (bit-and (aget this i'reglist) (bit-not (<< 1 i))))
                            )
                        )

                        (aset (aget this i'regfile) (aget this i'rd) reg_rn)
                        (§ assert (not (= (aget this i'rd) reg'PC)))
                        (§ break)
                    )
                    #_"LDR <Rt>, [<Rn>{,#<imm5>}]"
                    #_"0 1 1 0 1 imm5 Rn Rt"
                    (§ case code'LDR)
                    (§
                        (aset (aget this i'regfile) (aget this i'rt) (cpu''read32 this, (+ reg_rn (<< (aget this i'imm) 2))))
                        (§ assert (not (= (aget this i'rd) reg'PC)))
                        (§ break)
                    )
                    #_"LDR <Rt>,[SP{,#<imm8>}]"
                    #_"1 0 0 1 1 Rt imm8"
                    (§ case code'LDR_1)
                    (§
                        (aset (aget this i'regfile) (aget this i'rt) (cpu''read32 this, (+ reg_rn (<< (aget this i'imm) 2))))
                        (§ assert (not (= (aget this i'rd) reg'PC)))
                        (§ break)
                    )
                    #_"LDR <Rt>,<label>"
                    #_"0 1 0 0 1 Rt imm8"
                    (§ case code'LDR_2)
                    (§
                        (aset (aget this i'regfile) (aget this i'rt) (cpu''read32 this, (+ (bit-and (aget (aget this i'regfile) reg'PC) 0xfffffffc) (<< (aget this i'imm) 2) 4)))
                        (§ assert (not (= (aget this i'rd) reg'PC)))
                        (§ break)
                    )
                    #_"LDRB <Rt>,[<Rn>{,#<imm5>}]"
                    #_"0 1 1 1 1 imm5 Rn Rt"
                    (§ case code'LDRB)
                    (§
                        (aset (aget this i'regfile) (aget this i'rt) (cpu''read8 this, (+ reg_rn (aget this i'imm))))
                        (§ break)
                    )
                    #_"LDRH <Rt>,[<Rn>{,#<imm5>}]"
                    #_"1 0 0 0 1 imm5 Rn Rt"
                    (§ case code'LDRH)
                    (§
                        (aset (aget this i'regfile) (aget this i'rt) (cpu''read16 this, (+ reg_rn (<< (aget this i'imm) 1))))
                        (§ break)
                    )
                    #_"LSLS <Rd>,<Rm>,#<imm5>"
                    #_"0 0 0 0 0 imm5 Rm Rd"
                    #_"MOVS <Rd>,<Rm>"
                    #_"0 0 0 0 0 0 0 0 0 0 Rm Rd"
                 ;; (§ case code'MOVS_1)
                    (§ case code'LSLS)
                    (§
                        (if (zero? (aget this i'imm))
                            (do
                                ;; MOVS <Rd>,<Rm>
                                (§ ass reg_rd reg_rm)
                                (§ ass write_rd true)

                                ;; Update N and Z
                                (armv6m_update_n_z_flags this, reg_rd)
                            )
                            (do
                                ;; LSLS <Rd>,<Rm>,#<imm5>
                                (§ ass reg_rd (armv6m_shift_left this, reg_rm, (aget this i'imm), flags'NZC))
                                (§ ass write_rd true)
                            )
                        )
                        (§ break)
                    )
                    #_"LSRS <Rd>,<Rm>,#<imm5>"
                    #_"0 0 0 0 1 imm5 Rm Rd"
                    (§ case code'LSRS)
                    (§
                        (when (zero? (aget this i'imm))
                            (aset this i'imm 32)
                        )

                        (§ ass reg_rd (armv6m_shift_right this, reg_rm, (aget this i'imm), flags'NZC))
                        (§ ass write_rd true)
                        (§ break)
                    )
                    #_"MOVS <Rd>,#<imm8>"
                    #_"0 0 1 0 0 Rd imm8"
                    (§ case code'MOVS)
                    (§
                        (§ ass reg_rd (aget this i'imm))
                        (§ ass write_rd true)

                        (armv6m_update_n_z_flags this, reg_rd)
                        (§ break)
                    )
                    #_"STM <Rn>!,<registers>"
                    #_"1 1 0 0 0 Rn register_list"
                    (§ case code'STM)
                    (§
                        (§ ass #_"u32" addr reg_rn)

                        (§ for (§ ass #_"s32" i 0) (and (< i REGISTERS) (not (zero? (aget this i'reglist)))) (§ ass i (inc i))
                            (when-not (zero? (bit-and (aget this i'reglist) (<< 1 i)))
                                (cpu''write32 this, addr, (aget (aget this i'regfile) i))
                                (§ ass addr (+ addr 4))
                                (aset this i'reglist (bit-and (aget this i'reglist) (bit-not (<< 1 i))))
                            )
                        )

                        (§ ass reg_rd addr)
                        (§ ass write_rd true)
                        (§ break)
                    )
                    #_"STR <Rt>, [<Rn>{,#<imm5>}]"
                    #_"0 1 1 0 0 imm5 Rn Rt"
                    (§ case code'STR)
                    (§
                        (cpu''write32 this, (+ reg_rn (<< (aget this i'imm) 2)), (aget (aget this i'regfile) (aget this i'rt)))
                        (§ break)
                    )
                    #_"STR <Rt>,[SP,#<imm8>]"
                    #_"1 0 0 1 0 Rt imm8"
                    (§ case code'STR_1)
                    (§
                        (cpu''write32 this, (+ reg_rn (<< (aget this i'imm) 2)), (aget (aget this i'regfile) (aget this i'rt)))
                        (§ break)
                    )
                    #_"STRB <Rt>,[<Rn>,#<imm5>]"
                    #_"0 1 1 1 0 imm5 Rn Rt"
                    (§ case code'STRB)
                    (§
                        (cpu''write8 this, (+ reg_rn (aget this i'imm)), (aget (aget this i'regfile) (aget this i'rt)))
                        (§ break)
                    )
                    #_"STRH <Rt>,[<Rn>{,#<imm5>}]"
                    #_"1 0 0 0 0 imm5 Rn Rt"
                    (§ case code'STRH)
                    (§
                        (cpu''write16 this, (+ reg_rn (<< (aget this i'imm) 1)), (aget (aget this i'regfile) (aget this i'rt)))
                        (§ break)
                    )
                    #_"SUBS <Rdn>,#<imm8>"
                    #_"0 0 1 11 Rdn imm8"
                    (§ case code'SUBS_1)
                    (§
                        (§ ass reg_rd (armv6m_add_with_carry this, reg_rn, (bit-not (aget this i'imm)), 1, flags'all))
                        (§ ass write_rd true)
                        (§ break)
                    )
                )
                (§ break)
            )
            (§ case code'IGRP2)
            (§
                (§ switch (bit-and inst mask'IGRP2)
                    #_"ADDS <Rd>,<Rn>,#<imm3>"
                    #_"0 0 0 1 1 1 0 imm3 Rn Rd"
                    (§ case code'ADDS)
                    (§
                        (§ ass reg_rd (armv6m_add_with_carry this, reg_rn, (aget this i'imm), 0, flags'all))
                        (§ ass write_rd true)
                        (§ break)
                    )
                    #_"ADDS <Rd>,<Rn>,<Rm>"
                    #_"0 0 0 1 1 0 0 Rm Rn Rd"
                    (§ case code'ADDS_2)
                    (§
                        (§ ass reg_rd (armv6m_add_with_carry this, reg_rn, reg_rm, 0, flags'all))
                        (§ ass write_rd true)
                        (§ break)
                    )
                    #_"LDR <Rt>,[<Rn>,<Rm>]"
                    #_"0 1 0 1 1 0 0 Rm Rn Rt"
                    (§ case code'LDR_3)
                    (§
                        (aset (aget this i'regfile) (aget this i'rt) (cpu''read32 this, (+ reg_rn reg_rm)))
                        (§ assert (not (= (aget this i'rt) reg'PC)))
                        (§ break)
                    )
                    #_"LDRB <Rt>,[<Rn>,<Rm>]"
                    #_"0 1 0 1 1 1 0 Rm Rn Rt"
                    (§ case code'LDRB_1)
                    (§
                        (aset (aget this i'regfile) (aget this i'rt) (cpu''read8 this, (+ reg_rn reg_rm)))
                        (§ break)
                    )
                    #_"LDRH <Rt>,[<Rn>,<Rm>]"
                    #_"0 1 0 1 1 0 1 Rm Rn Rt"
                    (§ case code'LDRH_1)
                    (§
                        (aset (aget this i'regfile) (aget this i'rt) (cpu''read16 this, (+ reg_rn reg_rm)))
                        (§ break)
                    )
                    #_"LDRSB <Rt>,[<Rn>,<Rm>]"
                    #_"0 1 0 1 0 1 1 Rm Rn Rt"
                    (§ case code'LDRSB)
                    (§
                        (§ ass reg_rd (cpu''read8 this, (+ reg_rn reg_rm)))
                        (aset (aget this i'regfile) (aget this i'rt) (armv6m_sign_extend this, reg_rd, 8))
                        (§ break)
                    )
                    #_"LDRSH <Rt>,[<Rn>,<Rm>]"
                    #_"0 1 0 1 1 1 1 Rm Rn Rt"
                    (§ case code'LDRSH)
                    (§
                        (§ ass reg_rd (cpu''read16 this, (+ reg_rn reg_rm)))
                        (aset (aget this i'regfile) (aget this i'rt) (armv6m_sign_extend this, reg_rd, 16))
                        (§ break)
                    )
                    #_"POP <registers>"
                    #_"1 0 1 1 1 1 0 P register_list"
                    (§ case code'POP)
                    (§
                        (§ ass #_"u32" sp (aget (aget this i'regfile) reg'SP))

                        (§ for (§ ass #_"s32" i 0) (and (< i REGISTERS) (not (zero? (aget this i'reglist)))) (§ ass i (inc i))
                            (when-not (zero? (bit-and (aget this i'reglist) (<< 1 i)))
                                (aset (aget this i'regfile) i (cpu''read32 this, sp))

                                (§ ass sp (+ sp 4))

                                (when (= i reg'PC)
                                    (when-not (= (bit-and (aget (aget this i'regfile) i) EXC_RETURN) EXC_RETURN)
                                        (aset (aget this i'regfile) i (bit-and (aget (aget this i'regfile) i) (bit-not 1)))
                                    )
                                    (§ ass pc (aget (aget this i'regfile) i))
                                )

                                (aset this i'reglist (bit-and (aget this i'reglist) (bit-not (<< 1 i))))
                            )
                        )

                        (armv6m_update_sp this, sp)
                        (§ break)
                    )
                    #_"PUSH <registers>"
                    #_"1 0 1 1 0 1 0 M register_list"
                    (§ case code'PUSH)
                    (§
                        (§ ass #_"u32" sp (aget (aget this i'regfile) reg'SP))
                        (§ ass #_"u32" addr sp)
                        (§ ass #_"s32" bits_set 0)

                        (§ for (§ ass #_"s32" i 0) (< i REGISTERS) (§ ass i (inc i))
                            (when-not (zero? (bit-and (aget this i'reglist) (<< 1 i)))
                                (§ ass bits_set (inc bits_set))
                            )
                        )

                        (§ ass addr (- addr (* 4 bits_set)))

                        (§ for (§ ass #_"s32" i 0) (and (< i REGISTERS) (not (zero? (aget this i'reglist)))) (§ ass i (inc i))
                            (when-not (zero? (bit-and (aget this i'reglist) (<< 1 i)))
                                (cpu''write32 this, addr, (aget (aget this i'regfile) i))
                                (§ ass sp (- sp 4))
                                (§ ass addr (+ addr 4))
                                (aset this i'reglist (bit-and (aget this i'reglist) (bit-not (<< 1 i))))
                            )
                        )

                        (armv6m_update_sp this, sp)
                        (§ break)
                    )
                    #_"STR <Rt>,[<Rn>,<Rm>]"
                    #_"0 1 0 1 0 00 Rm Rn Rt"
                    (§ case code'STR_2)
                    (§
                        (cpu''write32 this, (+ reg_rn reg_rm), (aget (aget this i'regfile) (aget this i'rt)))
                        (§ break)
                    )
                    #_"STRB <Rt>,[<Rn>,<Rm>]"
                    #_"0 1 0 1 0 1 0 Rm Rn Rt"
                    (§ case code'STRB_1)
                    (§
                        (cpu''write8 this, (+ reg_rn reg_rm), (aget (aget this i'regfile) (aget this i'rt)))
                        (§ break)
                    )
                    #_"STRH <Rt>,[<Rn>,<Rm>]"
                    #_"0 1 0 1 0 0 1 Rm Rn Rt"
                    (§ case code'STRH_1)
                    (§
                        (cpu''write16 this, (+ reg_rn reg_rm), (aget (aget this i'regfile) (aget this i'rt)))
                        (§ break)
                    )
                    #_"SUBS <Rd>,<Rn>,#<imm3>"
                    #_"0 0 0 11 1 1 imm3 Rn Rd"
                    (§ case code'SUBS)
                    (§
                        (§ ass reg_rd (armv6m_add_with_carry this, reg_rn, (bit-not (aget this i'imm)), 1, flags'all))
                        (§ ass write_rd true)
                        (§ break)
                    )
                    #_"SUBS <Rd>,<Rn>,<Rm>"
                    #_"0 0 0 11 0 1 Rm Rn Rd"
                    (§ case code'SUBS_2)
                    (§
                        (§ ass reg_rd (armv6m_add_with_carry this, reg_rn, (bit-not reg_rm), 1, flags'all))
                        (§ ass write_rd true)
                        (§ break)
                    )
                )
                (§ break)
            )
            (§ case code'IGRP3)
            (§
                (§ switch (bit-and inst mask'IGRP3)
                    #_"ADD <Rdn>,<Rm>"
                    #_"0 1 0 0 0 1 0 0 Rm Rdn"
                    (§ case code'ADD)
                    (§
                        (§ ass reg_rd (+ reg_rn reg_rm))
                        (§ ass write_rd true)
                        (§ break)
                    )
                    #_"BKPT #<imm8>"
                    #_"1 0 1 1 1 1 1 0 imm8"
                    (§ case code'BKPT)
                    (§
                        ;; Not implemented
                        (§ break)
                    )
                    #_"CMP <Rn>,<Rm> <Rn> and <Rm> not both from R0-R7"
                    #_"0 1 0 0 0 1 0 1 N Rm Rn"
                    (§ case code'CMP_2)
                    (§
                        (§ ass reg_rd (armv6m_add_with_carry this, reg_rn, (bit-not reg_rm), 1, flags'all))
                        (§ break)
                    )
                    #_"MOV <Rd>,<Rm> Otherwise all versions of the Thumb instruction set."
                    #_"0 1 0 0 0 1 1 0 D Rm Rd"
                    (§ case code'MOV)
                    (§
                        (if (= (aget this i'rd) reg'PC)
                            (do
                                ;; Write to PC
                                (§ ass pc (bit-and reg_rm (bit-not 1)))

                                ;; Don't do normal writeback
                                (§ ass write_rd false)
                            )
                            (do
                                ;; Normal register
                                (§ ass reg_rd reg_rm)
                                (§ ass write_rd true)
                            )
                        )
                        (§ break)
                    )
                    #_"SVC #<imm8>"
                    #_"1 1 0 1 111 1 imm8"
                    (§ case code'SVC)
                    (§
                        (§ ass pc (armv6m_exception this, pc, 11))
                        (§ break)
                    )
                    #_"UDF #<imm8>"
                    #_"1 1 0 1 1 1 1 0 imm8"
                    (§ case code'UDF)
                    (§
                        ;; Not implemented
                        (§ break)
                    )
                )
                (§ break)
            )
            (§ case code'IGRP4)
            (§
                (§ switch (bit-and inst mask'IGRP4)
                    #_"ADD SP,SP,#<imm7>"
                    #_"1 0 1 1 0 0 0 0 0 imm7"
                    (§ case code'ADD_2)
                    (§
                        (§ ass reg_rd (+ reg_rn (<< (aget this i'imm) 2)))
                        (§ ass write_rd true)
                        (§ break)
                    )
                    #_"BLX <Rm>"
                    #_"0 1 0 0 0 1 1 1 1 Rm (0) (0) (0)"
                    (§ case code'BLX)
                    (§
                     ;; (aset this i'rd reg'LR)
                        (§ ass reg_rd (bit-or pc 1))
                        (§ ass write_rd true)

                        (§ ass pc (bit-and reg_rm (bit-not 1)))
                        (§ break)
                    )
                    #_"BX <Rm>"
                    #_"0 1 0 0 0 1 1 1 0 Rm (0) (0) (0)"
                    (§ case code'BX)
                    (§
                        (§ ass pc (bit-and reg_rm (bit-not 1)))
                        (§ break)
                    )
                    #_"SUB SP,SP,#<imm7>"
                    #_"1 0 1 1 000 0 1 imm7"
                    (§ case code'SUB)
                    (§
                        (§ ass reg_rd (- reg_rn (<< (aget this i'imm) 2)))
                        (§ ass write_rd true)
                        (§ break)
                    )
                )
                (§ break)
            )
            (§ case code'IGRP5)
            (§
                (§ switch (bit-and inst mask'IGRP5)
                    #_"ADCS <Rdn>,<Rm>"
                    #_"0 1 0 0 0 0 0 1 0 1 Rm Rdn"
                    (§ case code'ADCS)
                    (§
                        (§ ass reg_rd (armv6m_add_with_carry this, reg_rn, reg_rm, (if (zero? (bit-and (aget this i'apsr) flag'C)) 0 1), flags'all))
                        (§ ass write_rd true)
                        (§ break)
                    )
                    #_"ANDS <Rdn>,<Rm>"
                    #_"0 1 0 0 0 0 0 0 0 0 Rm Rdn"
                    (§ case code'ANDS)
                    (§
                        (§ ass reg_rd (bit-and reg_rn reg_rm))
                        (§ ass write_rd true)

                        (armv6m_update_n_z_flags this, reg_rd)
                        (§ break)
                    )
                    #_"ASRS <Rdn>,<Rm>"
                    #_"0 1 0 0 0 0 0 1 0 0 Rm Rdn"
                    (§ case code'ASRS_1)
                    (§
                        (§ ass reg_rd (armv6m_arith_shift_right this, reg_rn, reg_rm, flags'NZC))
                        (§ ass write_rd true)
                        (§ break)
                    )
                    #_"BICS <Rdn>,<Rm>"
                    #_"0 1 0 0 0 0 1 1 1 0 Rm Rdn"
                    (§ case code'BICS)
                    (§
                        (§ ass reg_rd (bit-and reg_rn (bit-not reg_rm)))
                        (§ ass write_rd true)

                        (armv6m_update_n_z_flags this, reg_rd)
                        (§ break)
                    )
                    #_"CMN <Rn>,<Rm>"
                    #_"0 1 0 0 0 0 1 0 1 1 Rm Rn"
                    (§ case code'CMN)
                    (§
                        (§ ass reg_rd (armv6m_add_with_carry this, reg_rn, reg_rm, 0, flags'all))
                        (§ break)
                    )
                    #_"CMP <Rn>,<Rm> <Rn> and <Rm> both from R0-R7"
                    #_"0 1 0 0 0 0 1 0 1 0 Rm Rn"
                    (§ case code'CMP_1)
                    (§
                        (§ ass reg_rd (armv6m_add_with_carry this, reg_rn, (bit-not reg_rm), 1, flags'all))
                        (§ break)
                    )
                    #_"EORS <Rdn>,<Rm>"
                    #_"0 1 0 0 0 0 0 0 0 1 Rm Rdn"
                    (§ case code'EORS)
                    (§
                        (§ ass reg_rd (bit-xor reg_rn reg_rm))
                        (§ ass write_rd true)

                        (armv6m_update_n_z_flags this, reg_rd)
                        (§ break)
                    )
                    #_"LSLS <Rdn>,<Rm>"
                    #_"0 1 0 0 0 0 0 0 1 0 Rm Rdn"
                    (§ case code'LSLS_1)
                    (§
                        (if (zero? reg_rm)
                            (do
                                (§ ass reg_rd reg_rn)
                                (§ ass write_rd true)

                                ;; Update N and Z
                                (armv6m_update_n_z_flags this, reg_rd)
                            )
                            (do
                                (§ ass reg_rd (armv6m_shift_left this, reg_rn, reg_rm, flags'NZC))
                                (§ ass write_rd true)
                            )
                        )
                        (§ break)
                    )
                    #_"LSRS <Rdn>,<Rm>"
                    #_"0 1 0 0 0 0 0 0 1 1 Rm Rdn"
                    (§ case code'LSRS_1)
                    (§
                        (§ ass reg_rd (armv6m_shift_right this, reg_rn, (bit-and reg_rm 0xff), flags'NZC))
                        (§ ass write_rd true)
                        (§ break)
                    )
                    #_"MULS <Rdm>,<Rn>,<Rdm>"
                    #_"0 1 0 0 0 0 1 1 0 1 Rn Rdm"
                    (§ case code'MULS)
                    (§
                        (§ ass reg_rd (* reg_rn reg_rm))
                        (§ ass write_rd true)

                        (armv6m_update_n_z_flags this, reg_rd)
                        (§ break)
                    )
                    #_"MVNS <Rd>,<Rm>"
                    #_"0 1 0 0 0 0 1 1 1 1 Rm Rd"
                    (§ case code'MVNS)
                    (§
                        (§ ass reg_rd (bit-not reg_rm))
                        (§ ass write_rd true)

                        (armv6m_update_n_z_flags this, reg_rd)
                        (§ break)
                    )
                    #_"ORRS <Rdn>,<Rm>"
                    #_"0 1 0 0 0 0 1 1 0 0 Rm Rdn"
                    (§ case code'ORRS)
                    (§
                        (§ ass reg_rd (bit-or reg_rn reg_rm))
                        (§ ass write_rd true)

                        (armv6m_update_n_z_flags this, reg_rd)
                        (§ break)
                    )
                    #_"REV <Rd>,<Rm>"
                    #_"1 0 1 1 1 0 1 0 0 0 Rm Rd"
                    (§ case code'REV)
                    (§
                        (§ ass reg_rd (bit-or (<< (bit-and (>>> reg_rm 0) 0xff) 24) (<< (bit-and (>>> reg_rm 8) 0xff) 16) (<< (bit-and (>>> reg_rm 16) 0xff) 8) (<< (bit-and (>>> reg_rm 24) 0xff) 0)))
                        (§ ass write_rd true)
                        (§ break)
                    )
                    #_"REV16 <Rd>,<Rm>"
                    #_"1 0 1 1 1 0 1 0 0 1 Rm Rd"
                    (§ case code'REV16)
                    (§
                        (§ ass reg_rd (bit-or (<< (bit-and (>>> reg_rm 0) 0xff) 8) (<< (bit-and (>>> reg_rm 8) 0xff) 0) (<< (bit-and (>>> reg_rm 16) 0xff) 24) (<< (bit-and (>>> reg_rm 24) 0xff) 16)))
                        (§ ass write_rd true)
                        (§ break)
                    )
                    #_"REVSH <Rd>,<Rm>"
                    #_"1 0 1 1 1 0 1 0 1 1 Rm Rd"
                    (§ case code'REVSH)
                    (§
                        (§ ass reg_rd (bit-or (<< (bit-and (>>> reg_rm 0) 0xff) 8) (<< (bit-and (>>> reg_rm 8) 0xff) 0)))
                        (§ ass reg_rd (armv6m_sign_extend this, reg_rd, 16))
                        (§ ass write_rd true)
                        (§ break)
                    )
                    #_"RORS <Rdn>,<Rm>"
                    #_"0 1 0 0 0 0 0 1 1 1 Rm Rdn"
                    (§ case code'RORS)
                    (§
                        (§ ass reg_rd (armv6m_rotate_right this, reg_rn, (bit-and reg_rm 0xff), flags'NZC))
                        (§ ass write_rd true)
                        (§ break)
                    )
                    #_"RSBS <Rd>,<Rn>,#0"
                    #_"0 1 0 0 0 0 1 0 0 1 Rn Rd"
                    (§ case code'RSBS)
                    (§
                        (§ ass reg_rd (armv6m_add_with_carry this, (bit-not reg_rn), 0, 1, flags'all))
                        (§ ass write_rd true)
                        (§ break)
                    )
                    #_"SBCS <Rdn>,<Rm>"
                    #_"0 1 0 0 0 0 0 1 1 0 Rm Rdn"
                    (§ case code'SBCS)
                    (§
                        (§ ass reg_rd (armv6m_add_with_carry this, reg_rn, (bit-not reg_rm), (if (zero? (bit-and (aget this i'apsr) flag'C)) 0 1), flags'all))
                        (§ ass write_rd true)
                        (§ break)
                    )
                    #_"SXTB <Rd>,<Rm>"
                    #_"1 0 1 1 100 0 0 1 Rm Rd"
                    (§ case code'SXTB)
                    (§
                        (§ ass reg_rd (bit-and reg_rm 0xff))
                        (when-not (zero? (bit-and reg_rd 0x80))
                            (§ ass reg_rd (bit-or reg_rd (<< (bit-not 0) 8)))
                        )
                        (§ ass write_rd true)
                        (§ break)
                    )
                    #_"SXTH <Rd>,<Rm>"
                    #_"1 0 1 1 100 0 0 0 Rm Rd"
                    (§ case code'SXTH)
                    (§
                        (§ ass reg_rd (bit-and reg_rm 0xffff))
                        (when-not (zero? (bit-and reg_rd 0x8000))
                            (§ ass reg_rd (bit-or reg_rd (<< (bit-not 0) 16)))
                        )
                        (§ ass write_rd true)
                        (§ break)
                    )
                    #_"TST <Rn>,<Rm>"
                    #_"000 1 0 0 1 0 0 0 Rm Rn"
                    (§ case code'TST)
                    (§
                        (§ ass reg_rd (bit-and reg_rn reg_rm))
                        ;; No writeback
                        (armv6m_update_n_z_flags this, reg_rd)
                        (§ break)
                    )
                    #_"UXTB <Rd>,<Rm>"
                    #_"1 0 1 1 100 0 1 1 Rm Rd"
                    (§ case code'UXTB)
                    (§
                        (§ ass reg_rd (bit-and reg_rm 0xff))
                        (§ ass write_rd true)
                        (§ break)
                    )
                    #_"UXTH <Rd>,<Rm>"
                    #_"1 0 1 1 100 0 1 0 Rm Rd"
                    (§ case code'UXTH)
                    (§
                        (§ ass reg_rd (bit-and reg_rm 0xffff))
                        (§ ass write_rd true)
                        (§ break)
                    )
                )
                (§ break)
            )
            (§ case code'IGRP6)
            (§
                (§ switch (bit-and inst mask'IGRP6)
                    #_"MRS <Rd>,<spec_reg>"
                    #_"1 1 1 01 0 1 1 1 1 1 (0) (1) (1) (1) (1) 1 0 (0) 0 Rd SYSm"
                    (§ case code'MRS)
                    (§
                        (§ ass #_"u32" sysm (bit-and (>>> inst2 0) 0xff))
                        (aset this i'rd (bit-and (>>> inst2 8) 0xf))

                        ;; Increment PC past second instruction word
                        (§ ass pc (+ pc 2))

                        (§ switch (bit-and (>>> sysm 3) 0x1f)
                            (§ case 0)
                            (§
                                (§ ass #_"u32" val 0)

                                (when-not (zero? (bit-and sysm 0x1))
                                    (§ ass val (bit-or val (bit-and (aget this i'ipsr) 0x1ff)))
                                )

                                (when (zero? (bit-and sysm 0x4))
                                    (§ ass val (bit-or val (bit-and (aget this i'apsr) 0xf8000000)))
                                )

                                (§ ass val (bit-or val (aget this i'ipsr)))
                                (§ ass val (bit-or val (aget this i'epsr)))

                                (§ ass reg_rd val)
                                (§ ass write_rd true)
                                (§ break)
                            )
                            (§ case 1)
                            (§
                                (§ switch (bit-and sysm 0x7)
                                    (§ case 0)
                                    (§
                                        ;; Main SP
                                        (§ ass reg_rd (aget this i'msp))
                                        (§ ass write_rd true)
                                        (§ break)
                                    )
                                    (§ case 1)
                                    (§
                                        ;; Process SP
                                        (§ ass reg_rd (aget this i'psp))
                                        (§ ass write_rd true)
                                        (§ break)
                                    )
                                )
                                (§ break)
                            )
                            (§ case 2)
                            (§
                                (§ switch (bit-and sysm 0x7)
                                    (§ case 0)
                                    (§
                                        ;; PRIMASK.PM
                                        (§ ass reg_rd (bit-and (aget this i'primask) PRIMASK_PM))
                                        (§ ass write_rd true)
                                        (§ break)
                                    )
                                    (§ case 4)
                                    (§
                                        ;; Control<1:0>
                                        (§ ass reg_rd (bit-and (aget this i'control) CONTROL_MASK))
                                        (§ ass write_rd true)
                                        (§ break)
                                    )
                                )
                                (§ break)
                            )
                        )
                        (§ break)
                    )
                    #_"MSR <spec_reg>,<Rn>"
                    #_"1 1 1 01 0 1 1 1 0 0 (0) Rn 1 0 (0) 0 (1) (0) (0) (0) SYSm"
                    (§ case code'MSR)
                    (§
                        (§ ass #_"u32" sysm (bit-and (>>> inst2 0) 0xff))

                        ;; Increment PC past second instruction word
                        (§ ass pc (+ pc 2))

                        (§ switch (bit-and (>>> sysm 3) 0x1f)
                            (§ case 0)
                            (§
                                (when (zero? (bit-and sysm 0x4))
                                    (aset this i'apsr (bit-and reg_rn 0xf8000000))
                                )
                                (§ break)
                            )
                            (§ case 1)
                            (§
                                ;; TODO: Only if privileged...
                                (§ switch (bit-and sysm 0x7)
                                    (§ case 0)
                                    (§
                                        ;; Main SP
                                        (aset this i'msp reg_rn)
                                        (§ break)
                                    )
                                    (§ case 1)
                                    (§
                                        ;; Process SP
                                        (aset this i'psp reg_rn)
                                        (§ break)
                                    )
                                )
                                (§ break)
                            )
                            (§ case 2)
                            (§
                                ;; TODO: Only if privileged...
                                (§ switch (bit-and sysm 0x7)
                                    (§ case 0)
                                    (§
                                        ;; PRIMASK.PM
                                        (aset this i'primask (bit-and reg_rn PRIMASK_PM))
                                        (§ break)
                                    )
                                    (§ case 4)
                                    (§
                                        ;; Control<1:0>
                                        (when-not (aget this i'handler?)
                                            (aset this i'control (bit-and reg_rn CONTROL_MASK))

                                            ;; Allow switching of current SP
                                         ;; (if-not (zero? (bit-and (aget this i'control) CONTROL_SPSEL))
                                         ;;     (§ ass spsel SP_MSP)
                                         ;;     (§ ass spsel SP_PSP)
                                         ;; )
                                        )
                                        (§ break)
                                    )
                                )
                                (§ break)
                            )
                        )
                        (§ break)
                    )
                    #_"CPS<effect> i"
                    #_"1 0 1 1 0 1 1 0 0 1 1 im (0) (0) (1) (0)"
                    (§ case code'CPS)
                    (§
                        ;; TODO: Only if privileged...

                        (if (zero? (aget this i'imm))
                            (do
                                ;; Enable
                                (aset this i'primask (bit-and (aget this i'primask) (bit-not PRIMASK_PM)))
                            )
                            (do
                                ;; Disable
                                (aset this i'primask (bit-or (aget this i'primask) PRIMASK_PM))
                            )
                        )
                        (§ break)
                    )
                )
                (§ break)
            )
            (§ case code'IGRP7)
            (§
                (§ switch (bit-and inst mask'IGRP7)
                    #_"DMB #<option>"
                    #_"1 1 1 01 0 1 1 1 0 1 1 (1) (1) (1) (1) 1 0 (0) 0 (1) (1) (1) (1) 0 1 0 1 option"
                 ;; (§ case code'DMB)
                    #_"DSB #<option>"
                    #_"1 1 1 01 0 1 1 1 0 1 1 (1) (1) (1) (1) 1 0 (0) 0 (1) (1) (1) (1) 0 1 0 0 option"
                 ;; (§ case code'DSB)
                    #_"ISB #<option>"
                    #_"1 1 1 01 0 1 1 1 0 1 1 (1) (1) (1) (1) 1 0 (0) 0 (1) (1) (1) (1) 0 1 1 0 option"
                    (§ case code'ISB)
                    (§
                        ;; Increment PC past second instruction word
                        (§ ass pc (+ pc 2))
                        (§ break)
                    )
                    #_"UDF_W #<imm16>"
                    #_"1 11 1 0 1 1 1 1 1 1 1 imm4 1 0 1 0 imm12"
                    (§ case code'UDF_W)
                    (§
                        ;; Increment PC past second instruction word
                        (§ ass pc (+ pc 2))
                        (§ break)
                    )
                )
                (§ break)
            )
            (§ case code'IGRP8)
            (§
                (§ switch (bit-and inst mask'IGRP8)
                    #_"NOP"
                    #_"1 0 1 1 1 1 1 1 0 0 0 0 0 0 0 0"
                    (§ case code'NOP)
                    (§
                        ;; Not implemented
                        (§ break)
                    )
                    #_"SEV"
                    #_"1 0 1 1 1 1 1 1 0 1 0 0 0 0 0 0"
                    (§ case code'SEV)
                    (§
                        ;; Not implemented
                        (§ break)
                    )
                    #_"WFE"
                    #_"1 0 1 1 1 1 1 1 0 0 1 0 0 0 0 0"
                    (§ case code'WFE)
                    (§
                        ;; Not implemented
                        (§ break)
                    )
                    #_"WFI"
                    #_"1 0 1 1 1 1 1 1 0 0 1 1 0 0 0 0"
                    (§ case code'WFI)
                    (§
                        ;; Not implemented
                        (§ break)
                    )
                    #_"YIELD"
                    #_"1 0 1 1 1 1 1 1 0 0 0 1 0 0 0 0"
                    (§ case code'YIELD)
                    (§
                        ;; Not implemented
                        (§ break)
                    )
                )
                (§ break)
            )
        )

        (when write_rd
            (if (= (aget this i'rd) reg'SP)
                (armv6m_update_sp this, reg_rd)
                (aset (aget this i'regfile) (aget this i'rd) reg_rd)
            )
        )

        ;; Can't perform a writeback to PC using normal mechanism as this is a special register...
        (when write_rd
            (§ assert (not (= (aget this i'rd) reg'PC)))
        )

        (aset (aget this i'regfile) reg'PC pc)
        nil
    )
)
