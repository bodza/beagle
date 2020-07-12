(ns beagle.armv6m
    (:refer-clojure :only [* + - < << <= = >> >>> aget and aset bit-and bit-not bit-or bit-xor byte-array cond cons dec defmacro defn first if-not inc next not object-array or pos? when when-not zero?])
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
    (def i'32_bit?    11) #_"bool"
    (def i'rd         12) #_"u32"
    (def i'rt         13) #_"u32"
    (def i'rm         14) #_"u32"
    (def i'rn         15) #_"u32"
    (def i'imm        16) #_"u32"
    (def i'cond       17) #_"u32"
    (def i'reglist    18) #_"u32"

    (def size'cpu     19)

    (defn #_"cpu" cpu'new [#_"ram" ram]
        (let [
            #_"cpu" this (object-array size'cpu)
        ]
            (aset this i'ram ram)
            (let [
                #_"[u32]" regs (object-array REGISTERS)
            ]
                (aset this i'regfile regs)

                (aset regs reg'SP          (cpu''read32 this,    (ram'base ram)))
                (aset regs reg'PC (bit-and (cpu''read32 this, (+ (ram'base ram) 4)) (bit-not 1)))

                (aset this i'msp (aget regs reg'SP))

                this
            )
        )
    )

    (defn #_"void" cpu''write8  [#_"cpu" this, #_"u32" addr, #_"u8"  data] (ram''write8  (aget this i'ram),          addr,              data) nil)
    (defn #_"void" cpu''write16 [#_"cpu" this, #_"u32" addr, #_"u16" data] (ram''write16 (aget this i'ram), (bit-and addr (bit-not 1)), data) nil)
    (defn #_"void" cpu''write32 [#_"cpu" this, #_"u32" addr, #_"u32" data] (ram''write32 (aget this i'ram), (bit-and addr (bit-not 3)), data) nil)

    (defn #_"u8"  cpu''read8  [#_"cpu" this, #_"u32" addr] (ram''read8  (aget this i'ram),          addr))
    (defn #_"u16" cpu''read16 [#_"cpu" this, #_"u32" addr] (ram''read16 (aget this i'ram), (bit-and addr (bit-not 1))))
    (defn #_"u32" cpu''read32 [#_"cpu" this, #_"u32" addr] (ram''read32 (aget this i'ram), (bit-and addr (bit-not 3))))

    (defn #_"cpu" cpu''step [#_"cpu" this]
        (let [
            #_"[u32]" regs (aget this i'regfile)
        ]
            (when (= (bit-and (aget regs reg'PC) EXC_RETURN) EXC_RETURN)
                (armv6m''exc_return this, (aget regs reg'PC))
            )
            (let [
                #_"u16" inst                                  (armv6m''read_inst this,    (aget regs reg'PC))
                #_"u16" inst2 (if (armv6m''decode this, inst) (armv6m''read_inst this, (+ (aget regs reg'PC) 2)) 0)
            ]
                (armv6m''execute this, inst, inst2)
                this
            )
        )
    )

    (defn #_"u16" armv6m''read_inst [#_"armv6m" this, #_"u32" addr]
        (if (zero? (bit-and addr 0x2))
            (bit-and (>>> (cpu''read32 this, addr)  0) 0xffff)
            (bit-and (>>> (cpu''read32 this, addr) 16) 0xffff)
        )
    )

    (defn #_"void" armv6m''update_sp [#_"armv6m" this, #_"u32" sp]
        (aset (aget this i'regfile) reg'SP sp)

        (if (or (zero? (bit-and (aget this i'control) CONTROL_SPSEL)) (aget this i'handler?))
            (aset this i'msp sp)
            (aset this i'psp sp)
        )
        nil
    )

    (defn #_"void" armv6m''update_rd [#_"armv6m" this, #_"u32" rd]
        (if (= (aget this i'rd) reg'SP)
            (armv6m''update_sp this, rd)
            (do
                (§ assert (not (= (aget this i'rd) reg'PC)))

                (aset (aget this i'regfile) (aget this i'rd) rd)
            )
        )
        nil
    )

    (defn #_"void" armv6m''update_nz [#_"armv6m" this, #_"u32" rd]
        (if (zero? rd) #_"Zero"
            (aset this i'apsr (bit-or  (aget this i'apsr)          flag'Z))
            (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'Z)))
        )

        (if-not (zero? (bit-and rd 0x80000000)) #_"Negative"
            (aset this i'apsr (bit-or  (aget this i'apsr)          flag'N))
            (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'N)))
        )
        nil
    )

    (defn #_"void" armv6m''update_pc [#_"armv6m" this, #_"u32" pc]
        (aset (aget this i'regfile) reg'PC pc)
        nil
    )

    (defn #_"u32" armv6m''add_with_carry [#_"armv6m" this, #_"u32" rn, #_"u32" rm, #_"u32" carry_in, #_"u32" mask]
        (let [
            #_"u32" res (+ rn rm carry_in)
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
                    #_"u64" unsigned_sum (+ (§ cast #_"u64" rn) (§ cast #_"u64" rm) carry_in)
                ]
                    (if (= unsigned_sum (§ cast #_"u64" res))
                        (aset this i'apsr (bit-and (aget this i'apsr) (bit-not flag'C)))
                        (aset this i'apsr (bit-or  (aget this i'apsr)          flag'C))
                    )
                )
            )

            (when-not (zero? (bit-and mask flag'V)) #_"oVerflow"
                (let [
                    #_"s64" signed_sum (+ (§ cast #_"s64" (§ cast #_"s32" rn)) (§ cast #_"s64" (§ cast #_"s32" rm)) carry_in)
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

    (defn #_"u32" armv6m''shift_left [#_"armv6m" this, #_"u32" val, #_"u32" shift, #_"u32" mask]
        (let [
            #_"u64" res (<< (§ cast #_"u64" val) shift)
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

    (defn #_"u32" armv6m''shift_right [#_"armv6m" this, #_"u32" val, #_"u32" shift, #_"u32" mask]
        (let [
            #_"u32" res (if (< shift 32) val 0)
        ]
            (when (and (not (zero? (bit-and mask flag'C))) (pos? shift)) #_"Carry out"
                (if (and (not (zero? (bit-and val (<< 1 (dec shift))))) (<= shift 32))
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

    (defn #_"u32" armv6m''arith_shift_right [#_"armv6m" this, #_"u32" val, #_"u32" shift, #_"u32" mask]
        (let [
            #_"s32" res (§ cast #_"s32" val)
        ]
            (when (and (not (zero? (bit-and mask flag'C))) (pos? shift)) #_"Carry out"
                (if-not (zero? (bit-and val (<< 1 (dec shift))))
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

    (defn #_"u32" armv6m''rotate_right [#_"armv6m" this, #_"u32" val, #_"u32" shift, #_"u32" mask]
        (let [
            #_"u32" res
                (if (zero? shift)
                    val
                    (let [
                        shift (bit-and shift 0x1f)
                    ]
                        (bit-or (>>> val shift) (<< val (- 32 shift)))
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

    (defn #_"u32" armv6m''sign_extend [#_"armv6m" this, #_"u32" val, #_"s32" offset]
        (if-not (zero? (bit-and val (<< 1 (dec offset))))
            (bit-or  val          (<< (bit-not 0) offset))
            (bit-and val (bit-not (<< (bit-not 0) offset)))
        )
    )

    (defn #_"u32" armv6m''exception [#_"armv6m" this, #_"u32" pc, #_"u32" exception]
        (let [
            #_"[u32]" regs (aget this i'regfile)
            #_"u32" sp
                (if (or (aget this i'handler?) (zero? (bit-and (aget this i'control) CONTROL_SPSEL)))
                    (aget this i'msp)
                    (aget this i'psp)
                )
            sp (- sp 4) _ (cpu''write32 this, sp, (aget this i'apsr))
            sp (- sp 4) _ (cpu''write32 this, sp, (aget regs reg'PC))
            sp (- sp 4) _ (cpu''write32 this, sp, (aget regs reg'LR))
            sp (- sp 4) _ (cpu''write32 this, sp, (aget regs     12))
            sp (- sp 4) _ (cpu''write32 this, sp, (aget regs      3))
            sp (- sp 4) _ (cpu''write32 this, sp, (aget regs      2))
            sp (- sp 4) _ (cpu''write32 this, sp, (aget regs      1))
            sp (- sp 4) _ (cpu''write32 this, sp, (aget regs      0))
        ]
            (aset regs reg'SP sp)
            (aset this i'ipsr (bit-and exception 0x3f))
            (aset regs reg'PC (bit-and (cpu''read32 this, (+ (ram'base (aget this i'ram)) (<< exception 2))) (bit-not 1)))

            (cond
                (aget this i'handler?)                                (aset regs reg'LR 0xfffffff1) #_"Return to handler mode (recursive interrupt?)"
                (zero? (bit-and (aget this i'control) CONTROL_SPSEL)) (aset regs reg'LR 0xfffffff9) #_"Return to thread mode (with main stack)"
                :else                                                 (aset regs reg'LR 0xfffffffd) #_"Return to thread mode (with process stack)"
            )

            (aset this i'handler? true)
            (aset this i'control (bit-and (aget this i'control) (bit-not CONTROL_SPSEL)))

            (aget regs reg'PC)
        )
    )

    (defn #_"void" armv6m''exc_return [#_"armv6m" this, #_"u32" pc]
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
                    :else (§ throw "Not handled")
                )

                (let [
                    #_"[u32]" regs (aget this i'regfile)
                    #_"u32" sp (aget regs reg'SP)
                    _ (aset regs      0 (cpu''read32 this, sp)) sp (+ sp 4)
                    _ (aset regs      1 (cpu''read32 this, sp)) sp (+ sp 4)
                    _ (aset regs      2 (cpu''read32 this, sp)) sp (+ sp 4)
                    _ (aset regs      3 (cpu''read32 this, sp)) sp (+ sp 4)
                    _ (aset regs     12 (cpu''read32 this, sp)) sp (+ sp 4)
                    _ (aset regs reg'LR (cpu''read32 this, sp)) sp (+ sp 4)
                    _ (aset regs reg'PC (cpu''read32 this, sp)) sp (+ sp 4)
                    _ (aset this i'apsr (cpu''read32 this, sp)) sp (+ sp 4)
                ]
                    (armv6m''update_sp this, sp)
                )
            )
        )
        nil
    )

    (defn #_"bool" armv6m''decode [#_"armv6m" this, #_"u16" inst]
        (aset this i'32_bit? false)
        (aset this i'rd 0)
        (aset this i'rt 0)
        (aset this i'rm 0)
        (aset this i'rn 0)
        (aset this i'imm 0)
        (aset this i'cond 0)
        (aset this i'reglist 0)

        (or
            (let [
                _ (aset this i'inst_group code'IGRP0)
                #_"u16" x (bit-and inst mask'IGRP0)
            ]
                (cond
                    (= x code'BCC) #_"BCC <label>" #_"1 1 0 1 cond imm8"
                    (do
                        (aset this i'cond (bit-and (>>> inst 8) 0x0f))
                        (aset this i'imm (bit-and (>>> inst 0) 0xff))
                        this
                    )
                )
            )

            (let [
                _ (aset this i'inst_group code'IGRP1)
                #_"u16" x (bit-and inst mask'IGRP1)
            ]
                (cond
                    (or
                        (= x code'ADDS_1) #_"ADDS <Rdn>,#<imm8>" #_"0 0 1 1 0 Rdn imm8"
                        (= x code'SUBS_1) #_"SUBS <Rdn>,#<imm8>" #_"0 0 1 1 1 Rdn imm8"
                    )
                    (do
                        (aset this i'rd (bit-and (>>> inst 8) 0x7))
                        (aset this i'rn (aget this i'rd))
                        (aset this i'imm (bit-and (>>> inst 0) 0xff))
                        this
                    )

                    (or
                        (= x code'ADR)  #_"ADR <Rd>,<label>"  #_"1 0 1 0 0 Rd imm8"
                        (= x code'MOVS) #_"MOVS <Rd>,#<imm8>" #_"0 0 1 0 0 Rd imm8"
                    )
                    (do
                        (aset this i'rd (bit-and (>>> inst 8) 0x7))
                        (aset this i'imm (bit-and (>>> inst 0) 0xff))
                        this
                    )

                    (or
                        (= x code'ASRS) #_"ASRS <Rd>,<Rm>,#<imm5>" #_"0 0 0 1 0 imm5 Rm Rd"
                        (= x code'LSLS) #_"LSLS <Rd>,<Rm>,#<imm5>" #_"0 0 0 0 0 imm5 Rm Rd"
                        (= x code'LSRS) #_"LSRS <Rd>,<Rm>,#<imm5>" #_"0 0 0 0 1 imm5 Rm Rd"
                    )
                    (do
                        (aset this i'imm (bit-and (>>> inst 6) 0x1f))
                        (aset this i'rm (bit-and (>>> inst 3) 0x7))
                        (aset this i'rd (bit-and (>>> inst 0) 0x7))
                        this
                    )

                    (= x code'B) #_"B <label>" #_"1 1 1 0 0 imm11"
                    (do
                        (aset this i'imm (bit-and (>>> inst 0) 0x7ff))
                        this
                    )

                    (= x code'BL) #_"BL <label>" #_"1 1 1 01 S imm10 1 1 J1 1 J2 imm11"
                    (do
                        (aset this i'32_bit? true)
                        (aset this i'imm (bit-and (>>> inst 0) 0x7ff))
                        (aset this i'rd reg'LR)

                        (when (= (bit-and (armv6m''read_inst this, (+ (aget (aget this i'regfile) reg'PC) 2)) 0xc000) 0xc000)
                            this
                        )
                    )

                    (= x code'CMP) #_"CMP <Rn>,#<imm8>" #_"0 0 1 0 1 Rn imm8"
                    (do
                        (aset this i'rn (bit-and (>>> inst 8) 0x7))
                        (aset this i'imm (bit-and (>>> inst 0) 0xff))
                        this
                    )

                    (or
                        (= x code'LDM)   #_"LDM <Rn>!,<registers> <Rn> not included in <registers>" #_"1 1 0 0 1 Rn register_list"
                        (= x code'LDM_1) #_"LDM <Rn>,<registers> <Rn> included in <registers>"      #_"1 1 0 0 1 Rn register_list"
                        (= x code'STM)   #_"STM <Rn>!,<registers>"                                  #_"1 1 0 0 0 Rn register_list"
                    )
                    (do
                        (aset this i'rn (bit-and (>>> inst 8) 0x7))
                        (aset this i'rd (aget this i'rn))
                        (aset this i'reglist (bit-and (>>> inst 0) 0xff))
                        this
                    )

                    (or
                        (= x code'LDR)  #_"LDR  <Rt>,[<Rn>{,#<imm5>}]" #_"0 1 1 0 1 imm5 Rn Rt"
                        (= x code'LDRB) #_"LDRB <Rt>,[<Rn>{,#<imm5>}]" #_"0 1 1 1 1 imm5 Rn Rt"
                        (= x code'LDRH) #_"LDRH <Rt>,[<Rn>{,#<imm5>}]" #_"1 0 0 0 1 imm5 Rn Rt"
                        (= x code'STR)  #_"STR  <Rt>,[<Rn>{,#<imm5>}]" #_"0 1 1 0 0 imm5 Rn Rt"
                        (= x code'STRB) #_"STRB <Rt>,[<Rn>,#<imm5>]"   #_"0 1 1 1 0 imm5 Rn Rt"
                        (= x code'STRH) #_"STRH <Rt>,[<Rn>{,#<imm5>}]" #_"1 0 0 0 0 imm5 Rn Rt"
                    )
                    (do
                        (aset this i'imm (bit-and (>>> inst 6) 0x1f))
                        (aset this i'rn (bit-and (>>> inst 3) 0x7))
                        (aset this i'rt (bit-and (>>> inst 0) 0x7))
                        (aset this i'rd (aget this i'rt))
                        this
                    )

                    (= x code'LDR_2) #_"LDR <Rt>,<label>" #_"0 1 0 0 1 Rt imm8"
                    (do
                        (aset this i'rt (bit-and (>>> inst 8) 0x7))
                        (aset this i'rd (aget this i'rt))
                        (aset this i'imm (bit-and (>>> inst 0) 0xff))
                        this
                    )

                    (or
                        (= x code'LDR_1) #_"LDR <Rt>,[SP{,#<imm8>}]" #_"1 0 0 1 1 Rt imm8"
                        (= x code'STR_1) #_"STR <Rt>,[SP,#<imm8>]"   #_"1 0 0 1 0 Rt imm8"
                        (= x code'ADD_1) #_"ADD <Rd>,SP,#<imm8>"     #_"1 0 1 0 1 Rd imm8"
                    )
                    (do
                        (aset this i'rt (bit-and (>>> inst 8) 0x7))
                        (aset this i'rn reg'SP)
                        (aset this i'rd (aget this i'rt))
                        (aset this i'imm (bit-and (>>> inst 0) 0xff))
                        this
                    )
                )
            )

            (let [
                _ (aset this i'inst_group code'IGRP2)
                #_"u16" x (bit-and inst mask'IGRP2)
            ]
                (cond
                    (or
                        (= x code'ADDS) #_"ADDS <Rd>,<Rn>,#<imm3>" #_"0 0 0 1 1 1 0 imm3 Rn Rd"
                        (= x code'SUBS) #_"SUBS <Rd>,<Rn>,#<imm3>" #_"0 0 0 1 1 1 1 imm3 Rn Rd"
                    )
                    (do
                        (aset this i'imm (bit-and (>>> inst 6) 0x7))
                        (aset this i'rn (bit-and (>>> inst 3) 0x7))
                        (aset this i'rd (bit-and (>>> inst 0) 0x7))
                        this
                    )

                    (or
                        (= x code'ADDS_2) #_"ADDS <Rd>,<Rn>,<Rm>" #_"0 0 0 1 1 0 0 Rm Rn Rd"
                        (= x code'SUBS_2) #_"SUBS <Rd>,<Rn>,<Rm>" #_"0 0 0 1 1 0 1 Rm Rn Rd"
                    )
                    (do
                        (aset this i'rm (bit-and (>>> inst 6) 0x7))
                        (aset this i'rn (bit-and (>>> inst 3) 0x7))
                        (aset this i'rd (bit-and (>>> inst 0) 0x7))
                        this
                    )

                    (or
                        (= x code'LDR_3)  #_"LDR   <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 1 0 0 Rm Rn Rt"
                        (= x code'LDRB_1) #_"LDRB  <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 1 1 0 Rm Rn Rt"
                        (= x code'LDRH_1) #_"LDRH  <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 1 0 1 Rm Rn Rt"
                        (= x code'LDRSB)  #_"LDRSB <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 0 1 1 Rm Rn Rt"
                        (= x code'LDRSH)  #_"LDRSH <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 1 1 1 Rm Rn Rt"
                        (= x code'STR_2)  #_"STR   <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 0 0 0 Rm Rn Rt"
                        (= x code'STRB_1) #_"STRB  <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 0 1 0 Rm Rn Rt"
                        (= x code'STRH_1) #_"STRH  <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 0 0 1 Rm Rn Rt"
                    )
                    (do
                        (aset this i'rm (bit-and (>>> inst 6) 0x7))
                        (aset this i'rn (bit-and (>>> inst 3) 0x7))
                        (aset this i'rt (bit-and (>>> inst 0) 0x7))
                        (aset this i'rd (aget this i'rt))
                        this
                    )

                    (= x code'POP) #_"POP <registers>" #_"1 0 1 1 1 1 0 P register_list"
                    (do
                        (aset this i'reglist (bit-and (>>> inst 0) 0xff))
                        (when-not (zero? (bit-and inst (<< 1 8)))
                            (aset this i'reglist (bit-or (aget this i'reglist) (<< 1 reg'PC)))
                        )
                        this
                    )

                    (= x code'PUSH) #_"PUSH <registers>" #_"1 0 1 1 0 1 0 M register_list"
                    (do
                        (aset this i'reglist (bit-and (>>> inst 0) 0xff))
                        (when-not (zero? (bit-and inst (<< 1 8)))
                            (aset this i'reglist (bit-or (aget this i'reglist) (<< 1 reg'LR)))
                        )
                        this
                    )
                )
            )

            (let [
                _ (aset this i'inst_group code'IGRP3)
                #_"u16" x (bit-and inst mask'IGRP3)
            ]
                (cond
                    (= x code'ADD) #_"ADD <Rdn>,<Rm>" #_"0 1 0 0 0 1 0 0 Rm Rdn"
                    (do
                        (aset this i'rm (bit-and (>>> inst 3) 0xf))
                        (aset this i'rd (bit-and (>>> inst 0) 0x7))
                        (aset this i'rd (bit-or (aget this i'rd) (bit-and (>>> inst 4) 0x8)))
                        (aset this i'rn (aget this i'rd))
                        this
                    )

                    (or
                        (= x code'BKPT) #_"BKPT #<imm8>" #_"1 0 1 1 1 1 1 0 imm8"
                        (= x code'SVC)  #_"SVC  #<imm8>" #_"1 1 0 1 1 1 1 1 imm8"
                        (= x code'UDF)  #_"UDF  #<imm8>" #_"1 1 0 1 1 1 1 0 imm8"
                    )
                    (do
                        (aset this i'imm (bit-and (>>> inst 0) 0xff))
                        this
                    )

                    (= x code'CMP_2) #_"CMP <Rn>,<Rm> <Rn> and <Rm> not both from R0-R7" #_"0 1 0 0 0 1 0 1 N Rm Rn"
                    (do
                        (aset this i'rm (bit-and (>>> inst 3) 0xf))
                        (aset this i'rn (bit-and (>>> inst 0) 0x7))
                        (aset this i'rn (bit-or (aget this i'rn) (bit-and (>>> inst 4) 0x8)))
                        this
                    )

                    (= x code'MOV) #_"MOV <Rd>,<Rm> Otherwise all versions of the Thumb instruction set." #_"0 1 0 0 0 1 1 0 D Rm Rd"
                    (do
                        (aset this i'rm (bit-and (>>> inst 3) 0xf))
                        (aset this i'rd (bit-and (>>> inst 0) 0x7))
                        (aset this i'rd (bit-or (aget this i'rd) (bit-and (>>> inst 4) 0x8)))
                        this
                    )
                )
            )

            (let [
                _ (aset this i'inst_group code'IGRP4)
                #_"u16" x (bit-and inst mask'IGRP4)
            ]
                (cond
                    (or
                        (= x code'ADD_2) #_"ADD SP,SP,#<imm7>" #_"1 0 1 1 0 0 0 0 0 imm7"
                        (= x code'SUB)   #_"SUB SP,SP,#<imm7>" #_"1 0 1 1 0 0 0 0 1 imm7"
                    )
                    (do
                        (aset this i'rn reg'SP)
                        (aset this i'rd reg'SP)
                        (aset this i'imm (bit-and (>>> inst 0) 0x7f))
                        this
                    )

                    (= x code'BLX) #_"BLX <Rm>" #_"0 1 0 0 0 1 1 1 1 Rm (0) (0) (0)"
                    (do
                        (aset this i'rm (bit-and (>>> inst 3) 0xf))
                        (aset this i'rd reg'LR)
                        this
                    )

                    (= x code'BX) #_"BX <Rm>" #_"0 1 0 0 0 1 1 1 0 Rm (0) (0) (0)"
                    (do
                        (aset this i'rm (bit-and (>>> inst 3) 0xf))
                        this
                    )
                )
            )

            (let [
                _ (aset this i'inst_group code'IGRP5)
                #_"u16" x (bit-and inst mask'IGRP5)
            ]
                (cond
                    (or
                        (= x code'ADCS)   #_"ADCS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 1 0 1 Rm Rdn"
                        (= x code'ANDS)   #_"ANDS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 0 0 0 Rm Rdn"
                        (= x code'ASRS_1) #_"ASRS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 1 0 0 Rm Rdn"
                        (= x code'BICS)   #_"BICS <Rdn>,<Rm>" #_"0 1 0 0 0 0 1 1 1 0 Rm Rdn"
                        (= x code'EORS)   #_"EORS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 0 0 1 Rm Rdn"
                        (= x code'LSLS_1) #_"LSLS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 0 1 0 Rm Rdn"
                        (= x code'LSRS_1) #_"LSRS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 0 1 1 Rm Rdn"
                        (= x code'ORRS)   #_"ORRS <Rdn>,<Rm>" #_"0 1 0 0 0 0 1 1 0 0 Rm Rdn"
                        (= x code'RORS)   #_"RORS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 1 1 1 Rm Rdn"
                        (= x code'SBCS)   #_"SBCS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 1 1 0 Rm Rdn"
                    )
                    (do
                        (aset this i'rm (bit-and (>>> inst 3) 0x7))
                        (aset this i'rd (bit-and (>>> inst 0) 0x7))
                        (aset this i'rn (aget this i'rd))
                        this
                    )

                    (or
                        (= x code'CMN)   #_"CMN <Rn>,<Rm>"                               #_"0 1 0 0 0 0 1 0 1 1 Rm Rn"
                        (= x code'CMP_1) #_"CMP <Rn>,<Rm> <Rn> and <Rm> both from R0-R7" #_"0 1 0 0 0 0 1 0 1 0 Rm Rn"
                        (= x code'TST)   #_"TST <Rn>,<Rm>"                               #_"0 0 0 1 0 0 1 0 0 0 Rm Rn"
                    )
                    (do
                        (aset this i'rm (bit-and (>>> inst 3) 0x7))
                        (aset this i'rn (bit-and (>>> inst 0) 0x7))
                        this
                    )

                    (= x code'MULS) #_"MULS <Rdm>,<Rn>,<Rdm>" #_"0 1 0 0 0 0 1 1 0 1 Rn Rdm"
                    (do
                        (aset this i'rn (bit-and (>>> inst 3) 0x7))
                        (aset this i'rd (bit-and (>>> inst 0) 0x7))
                        (aset this i'rm (aget this i'rd))
                        this
                    )

                    (or
                        (= x code'MVNS)  #_"MVNS  <Rd>,<Rm>" #_"0 1 0 0 0 0 1 1 1 1 Rm Rd"
                        (= x code'REV)   #_"REV   <Rd>,<Rm>" #_"1 0 1 1 1 0 1 0 0 0 Rm Rd"
                        (= x code'REV16) #_"REV16 <Rd>,<Rm>" #_"1 0 1 1 1 0 1 0 0 1 Rm Rd"
                        (= x code'REVSH) #_"REVSH <Rd>,<Rm>" #_"1 0 1 1 1 0 1 0 1 1 Rm Rd"
                        (= x code'SXTB)  #_"SXTB  <Rd>,<Rm>" #_"1 0 1 1 1 0 0 0 0 1 Rm Rd"
                        (= x code'SXTH)  #_"SXTH  <Rd>,<Rm>" #_"1 0 1 1 1 0 0 0 0 0 Rm Rd"
                        (= x code'UXTB)  #_"UXTB  <Rd>,<Rm>" #_"1 0 1 1 1 0 0 0 1 1 Rm Rd"
                        (= x code'UXTH)  #_"UXTH  <Rd>,<Rm>" #_"1 0 1 1 1 0 0 0 1 0 Rm Rd"
                    )
                    (do
                        (aset this i'rm (bit-and (>>> inst 3) 0x7))
                        (aset this i'rd (bit-and (>>> inst 0) 0x7))
                        this
                    )

                    (= x code'RSBS) #_"RSBS <Rd>,<Rn>,#0" #_"0 1 0 0 0 0 1 0 0 1 Rn Rd"
                    (do
                        (aset this i'rn (bit-and (>>> inst 3) 0x7))
                        (aset this i'rd (bit-and (>>> inst 0) 0x7))
                        this
                    )
                )
            )

            (let [
                _ (aset this i'inst_group code'IGRP6)
                #_"u16" x (bit-and inst mask'IGRP6)
            ]
                (cond
                    (= x code'MRS) #_"MRS <Rd>,<spec_reg>" #_"1 1 1 0 1 0 1 1 1 1 1 (0) (1) (1) (1) (1) 1 0 (0) 0 Rd SYSm"
                    (do
                        (aset this i'32_bit? true)
                        this
                    )

                    (= x code'MSR) #_"MSR <spec_reg>,<Rn>" #_"1 1 1 0 1 0 1 1 1 0 0 (0) Rn 1 0 (0) 0 (1) (0) (0) (0) SYSm"
                    (do
                        (aset this i'32_bit? true)
                        (aset this i'rn (bit-and (>>> inst 0) 0xf))
                        this
                    )

                    (= x code'CPS) #_"CPS<effect> i" #_"1 0 1 1 0 1 1 0 0 1 1 im (0) (0) (1) (0)"
                    (do
                        (aset this i'imm (bit-and (>>> inst 4) 0x1))
                        this
                    )
                )
            )

            (let [
                _ (aset this i'inst_group code'IGRP7)
                #_"u16" x (bit-and inst mask'IGRP7)
            ]
                (cond
                    (or
                        (= x code'DMB)   #_"DMB #<option>"  #_"1 1 1 0 1 0 1 1 1 0 1 1 (1) (1) (1) (1) 1 0 (0) 0 (1) (1) (1) (1) 0 1 0 1 option"
                        (= x code'DSB)   #_"DSB #<option>"  #_"1 1 1 0 1 0 1 1 1 0 1 1 (1) (1) (1) (1) 1 0 (0) 0 (1) (1) (1) (1) 0 1 0 0 option"
                        (= x code'ISB)   #_"ISB #<option>"  #_"1 1 1 0 1 0 1 1 1 0 1 1 (1) (1) (1) (1) 1 0 (0) 0 (1) (1) (1) (1) 0 1 1 0 option"
                        (= x code'UDF_W) #_"UDF_W #<imm16>" #_"1 1 1 1 0 1 1 1 1 1 1 1 imm4 1 0 1 0 imm12"
                    )
                    (do
                        (aset this i'32_bit? true)
                        this
                    )
                )
            )

            (let [
                _ (aset this i'inst_group code'IGRP8)
                #_"u16" x (bit-and inst mask'IGRP8)
            ]
                (cond
                    (or
                        (= x code'NOP)   #_"NOP"   #_"1 0 1 1 1 1 1 1 0 0 0 0 0 0 0 0"
                        (= x code'SEV)   #_"SEV"   #_"1 0 1 1 1 1 1 1 0 1 0 0 0 0 0 0"
                        (= x code'WFE)   #_"WFE"   #_"1 0 1 1 1 1 1 1 0 0 1 0 0 0 0 0"
                        (= x code'WFI)   #_"WFI"   #_"1 0 1 1 1 1 1 1 0 0 1 1 0 0 0 0"
                        (= x code'YIELD) #_"YIELD" #_"1 0 1 1 1 1 1 1 0 0 0 1 0 0 0 0"
                    )
                    (do
                        this
                    )
                )
            )

            (§ throw "Instruction decode failed")
        )

        (aget this i'32_bit?)
    )

    (defn #_"void" armv6m''execute [#_"armv6m" this, #_"u16" inst, #_"u16" inst2]
        (let [
            #_"[u32]" regs (aget this i'regfile)
            #_"u32" reg_rm (aget regs (aget this i'rm))
            #_"u32" reg_rn (aget regs (aget this i'rn))
            #_"u32" pc (+ (aget regs reg'PC) 2)
            #_"s32" inst_group (aget this i'inst_group)
        ]
            (cond
                (= inst_group code'IGRP0)
                (let [
                    #_"u16" op (bit-and inst mask'IGRP0)
                ]
                    (cond
                        (= op code'BCC) #_"BCC <label>" #_"1 1 0 1 cond imm8"
                        (let [
                            #_"u32" offset (armv6m''sign_extend this, (aget this i'imm), 8)
                            offset (<< offset 1)
                            offset (+ offset pc 2)
                            #_"u32" kond (aget this i'cond)
                            #_"u32" apsr (aget this i'apsr)
                            pc
                                (cond
                                    (= kond  0) (if-not (zero? (bit-and apsr flag'Z)) offset pc) #_"EQ"
                                    (= kond  1) (if     (zero? (bit-and apsr flag'Z)) offset pc) #_"NE"
                                    (= kond  2) (if-not (zero? (bit-and apsr flag'C)) offset pc) #_"CS/HS"
                                    (= kond  3) (if     (zero? (bit-and apsr flag'C)) offset pc) #_"CC/LO"
                                    (= kond  4) (if-not (zero? (bit-and apsr flag'N)) offset pc) #_"MI"
                                    (= kond  5) (if     (zero? (bit-and apsr flag'N)) offset pc) #_"PL"
                                    (= kond  6) (if-not (zero? (bit-and apsr flag'V)) offset pc) #_"VS"
                                    (= kond  7) (if     (zero? (bit-and apsr flag'V)) offset pc) #_"VC"
                                    (= kond  8) (if (and (not (zero? (bit-and apsr flag'C)))     (zero? (bit-and apsr flag'Z)))  offset pc) #_"HI"
                                    (= kond  9) (if (or       (zero? (bit-and apsr flag'C)) (not (zero? (bit-and apsr flag'Z)))) offset pc) #_"LS"
                                    (= kond 10) (if     (= (>>> (bit-and apsr flag'N) shift'N) (>>> (bit-and apsr flag'V) shift'V)) offset pc) #_"GE"
                                    (= kond 11) (if-not (= (>>> (bit-and apsr flag'N) shift'N) (>>> (bit-and apsr flag'V) shift'V)) offset pc) #_"LT"
                                    (= kond 12) (if (and     (zero? (bit-and apsr flag'Z))       (= (>>> (bit-and apsr flag'N) shift'N) (>>> (bit-and apsr flag'V) shift'V)))  offset pc) #_"GT"
                                    (= kond 13) (if (or (not (zero? (bit-and apsr flag'Z))) (not (= (>>> (bit-and apsr flag'N) shift'N) (>>> (bit-and apsr flag'V) shift'V)))) offset pc) #_"LE"
                                    (= kond 14) offset #_"AL"
                                    (= kond 15) (armv6m''exception this, pc, 11) #_"SVC"
                                    :else (§ throw "Bad condition code")
                                )
                        ]
                            (armv6m''update_pc pc)
                        )
                    )
                )

                (= inst_group code'IGRP1)
                (let [
                    #_"u16" op (bit-and inst mask'IGRP1)
                ]
                    (cond
                        (= op code'ADDS_1) #_"ADDS <Rdn>,#<imm8>" #_"0 0 1 1 0 Rdn imm8"
                        (do
                            (armv6m''update_rd this, (armv6m''add_with_carry this, reg_rn, (aget this i'imm), 0, flags'all))
                            (armv6m''update_pc pc)
                        )
                        (= op code'ADD_1) #_"ADD <Rd>,SP,#<imm8>" #_"1 0 1 0 1 Rd imm8"
                        (do
                            (armv6m''update_rd this, (+ reg_rn (<< (aget this i'imm) 2)))
                            (armv6m''update_pc pc)
                        )
                        (= op code'ADR) #_"ADR <Rd>,<label>" #_"1 0 1 0 0 Rd imm8"
                        (do
                            (armv6m''update_rd this, (+ pc (aget this i'imm) 2))
                            (armv6m''update_pc pc)
                        )
                        (= op code'ASRS) #_"ASRS <Rd>,<Rm>,#<imm5>" #_"0 0 0 1 0 imm5 Rm Rd"
                        (do
                            (when (zero? (aget this i'imm))
                                (aset this i'imm 32)
                            )
                            (armv6m''update_rd this, (armv6m''arith_shift_right this, reg_rm, (aget this i'imm), flags'NZC))
                            (armv6m''update_pc pc)
                        )
                        (= op code'B) #_"B <label>" #_"1 1 1 0 0 imm11"
                        (let [
                            #_"u32" offset (armv6m''sign_extend this, (aget this i'imm), 11)
                            offset (<< offset 1)
                            offset (+ offset pc 2)
                        ]
                            (armv6m''update_pc offset)
                        )
                        (= op code'BL) #_"BL <label>" #_"1 1 1 0 1 S imm10 1 1 J1 1 J2 imm11"
                        (let [
                            #_"u32" offset (armv6m''sign_extend this, (aget this i'imm), 11)
                            offset (<< offset 11)
                            _ (aset this i'imm (bit-and (>>> inst2 0) 0x7ff))
                            offset (bit-or offset (aget this i'imm))
                            offset (<< offset 1)
                            offset (+ offset pc)
                        ]
                         ;; (aset this i'rd reg'LR)
                            (armv6m''update_rd this, (bit-or (+ pc 2) 1))
                            (armv6m''update_pc (+ offset 2))
                        )
                        (= op code'CMP) #_"CMP <Rn>,#<imm8>" #_"0 0 1 0 1 Rn imm8"
                        (do
                            (armv6m''add_with_carry this, reg_rn, (bit-not (aget this i'imm)), 1, flags'all)
                            (armv6m''update_pc pc)
                        )
                        (or
                            (= op code'LDM)   #_"LDM <Rn>!,<registers> <Rn> not included in <registers>" #_"1 1 0 0 1 Rn register_list"
                            (= op code'LDM_1) #_"LDM <Rn>,<registers> <Rn> included in <registers>"      #_"1 1 0 0 1 Rn register_list"
                        )
                        (do
                            (§ ass #_"u32" addr reg_rn)

                            (§ for (§ ass #_"s32" i 0) (and (< i REGISTERS) (not (zero? (aget this i'reglist)))) (§ ass i (inc i))
                                (when-not (zero? (bit-and (aget this i'reglist) (<< 1 i)))
                                    (aset regs i (cpu''read32 this, addr))
                                    (when (= i reg'PC)
                                        (when-not (= (bit-and (aget regs reg'PC) EXC_RETURN) EXC_RETURN)
                                            (armv6m''update_pc (bit-and (aget regs reg'PC) (bit-not 1)))
                                        )
                                        (§ ass pc (aget regs i))
                                    )
                                    (§ ass addr (+ addr 4))
                                    (aset this i'reglist (bit-and (aget this i'reglist) (bit-not (<< 1 i))))
                                )
                            )

                            (aset regs (aget this i'rd) addr)
                            (§ assert (not (= (aget this i'rd) reg'PC)))
                            (armv6m''update_pc pc)
                        )
                        (= op code'LDR) #_"LDR <Rt>, [<Rn>{,#<imm5>}]" #_"0 1 1 0 1 imm5 Rn Rt"
                        (do
                            (aset regs (aget this i'rt) (cpu''read32 this, (+ reg_rn (<< (aget this i'imm) 2))))
                            (§ assert (not (= (aget this i'rt) reg'PC)))
                            (armv6m''update_pc pc)
                        )
                        (= op code'LDR_1) #_"LDR <Rt>,[SP{,#<imm8>}]" #_"1 0 0 1 1 Rt imm8"
                        (do
                            (aset regs (aget this i'rt) (cpu''read32 this, (+ reg_rn (<< (aget this i'imm) 2))))
                            (§ assert (not (= (aget this i'rt) reg'PC)))
                            (armv6m''update_pc pc)
                        )
                        (= op code'LDR_2) #_"LDR <Rt>,<label>" #_"0 1 0 0 1 Rt imm8"
                        (do
                            (aset regs (aget this i'rt) (cpu''read32 this, (+ (bit-and (aget regs reg'PC) 0xfffffffc) (<< (aget this i'imm) 2) 4)))
                            (§ assert (not (= (aget this i'rt) reg'PC)))
                            (armv6m''update_pc pc)
                        )
                        (= op code'LDRB) #_"LDRB <Rt>,[<Rn>{,#<imm5>}]" #_"0 1 1 1 1 imm5 Rn Rt"
                        (do
                            (aset regs (aget this i'rt) (cpu''read8 this, (+ reg_rn (aget this i'imm))))
                            (armv6m''update_pc pc)
                        )
                        (= op code'LDRH) #_"LDRH <Rt>,[<Rn>{,#<imm5>}]" #_"1 0 0 0 1 imm5 Rn Rt"
                        (do
                            (aset regs (aget this i'rt) (cpu''read16 this, (+ reg_rn (<< (aget this i'imm) 1))))
                            (armv6m''update_pc pc)
                        )
                        (or
                            (= op code'MOVS_1) #_"MOVS <Rd>,<Rm>"         #_"0 0 0 0 0 0 0 0 0 0 Rm Rd"
                            (= op code'LSLS)   #_"LSLS <Rd>,<Rm>,#<imm5>" #_"0 0 0 0 0 imm5 Rm Rd"
                        )
                        (do
                            (if (zero? (aget this i'imm))
                                (do
                                    (armv6m''update_rd this, reg_rm)
                                    (armv6m''update_nz this, reg_rm)
                                )
                                (do
                                    (armv6m''update_rd this, (armv6m''shift_left this, reg_rm, (aget this i'imm), flags'NZC))
                                )
                            )
                            (armv6m''update_pc pc)
                        )
                        (= op code'LSRS) #_"LSRS <Rd>,<Rm>,#<imm5>" #_"0 0 0 0 1 imm5 Rm Rd"
                        (do
                            (when (zero? (aget this i'imm))
                                (aset this i'imm 32)
                            )
                            (armv6m''update_rd this, (armv6m''shift_right this, reg_rm, (aget this i'imm), flags'NZC))
                            (armv6m''update_pc pc)
                        )
                        (= op code'MOVS) #_"MOVS <Rd>,#<imm8>" #_"0 0 1 0 0 Rd imm8"
                        (let [
                            #_"u32" reg_rd (aget this i'imm)
                        ]
                            (armv6m''update_rd this, reg_rd)
                            (armv6m''update_nz this, reg_rd)
                            (armv6m''update_pc pc)
                        )
                        (= op code'STM) #_"STM <Rn>!,<registers>" #_"1 1 0 0 0 Rn register_list"
                        (do
                            (§ ass #_"u32" addr reg_rn)

                            (§ for (§ ass #_"s32" i 0) (and (< i REGISTERS) (not (zero? (aget this i'reglist)))) (§ ass i (inc i))
                                (when-not (zero? (bit-and (aget this i'reglist) (<< 1 i)))
                                    (cpu''write32 this, addr, (aget regs i))
                                    (§ ass addr (+ addr 4))
                                    (aset this i'reglist (bit-and (aget this i'reglist) (bit-not (<< 1 i))))
                                )
                            )

                            (armv6m''update_rd this, addr)
                            (armv6m''update_pc pc)
                        )
                        (= op code'STR) #_"STR <Rt>, [<Rn>{,#<imm5>}]" #_"0 1 1 0 0 imm5 Rn Rt"
                        (do
                            (cpu''write32 this, (+ reg_rn (<< (aget this i'imm) 2)), (aget regs (aget this i'rt)))
                            (armv6m''update_pc pc)
                        )
                        (= op code'STR_1) #_"STR <Rt>,[SP,#<imm8>]" #_"1 0 0 1 0 Rt imm8"
                        (do
                            (cpu''write32 this, (+ reg_rn (<< (aget this i'imm) 2)), (aget regs (aget this i'rt)))
                            (armv6m''update_pc pc)
                        )
                        (= op code'STRB) #_"STRB <Rt>,[<Rn>,#<imm5>]" #_"0 1 1 1 0 imm5 Rn Rt"
                        (do
                            (cpu''write8 this, (+ reg_rn (aget this i'imm)), (aget regs (aget this i'rt)))
                            (armv6m''update_pc pc)
                        )
                        (= op code'STRH) #_"STRH <Rt>,[<Rn>{,#<imm5>}]" #_"1 0 0 0 0 imm5 Rn Rt"
                        (do
                            (cpu''write16 this, (+ reg_rn (<< (aget this i'imm) 1)), (aget regs (aget this i'rt)))
                            (armv6m''update_pc pc)
                        )
                        (= op code'SUBS_1) #_"SUBS <Rdn>,#<imm8>" #_"0 0 1 1 1 Rdn imm8"
                        (do
                            (armv6m''update_rd this, (armv6m''add_with_carry this, reg_rn, (bit-not (aget this i'imm)), 1, flags'all))
                            (armv6m''update_pc pc)
                        )
                    )
                )

                (= inst_group code'IGRP2)
                (let [
                    #_"u16" op (bit-and inst mask'IGRP2)
                ]
                    (cond
                        (= op code'ADDS) #_"ADDS <Rd>,<Rn>,#<imm3>" #_"0 0 0 1 1 1 0 imm3 Rn Rd"
                        (do
                            (armv6m''update_rd this, (armv6m''add_with_carry this, reg_rn, (aget this i'imm), 0, flags'all))
                            (armv6m''update_pc pc)
                        )
                        (= op code'ADDS_2) #_"ADDS <Rd>,<Rn>,<Rm>" #_"0 0 0 1 1 0 0 Rm Rn Rd"
                        (do
                            (armv6m''update_rd this, (armv6m''add_with_carry this, reg_rn, reg_rm, 0, flags'all))
                            (armv6m''update_pc pc)
                        )
                        (= op code'LDR_3) #_"LDR <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 1 0 0 Rm Rn Rt"
                        (do
                            (aset regs (aget this i'rt) (cpu''read32 this, (+ reg_rn reg_rm)))
                            (§ assert (not (= (aget this i'rt) reg'PC)))
                            (armv6m''update_pc pc)
                        )
                        (= op code'LDRB_1) #_"LDRB <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 1 1 0 Rm Rn Rt"
                        (do
                            (aset regs (aget this i'rt) (cpu''read8 this, (+ reg_rn reg_rm)))
                            (armv6m''update_pc pc)
                        )
                        (= op code'LDRH_1) #_"LDRH <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 1 0 1 Rm Rn Rt"
                        (do
                            (aset regs (aget this i'rt) (cpu''read16 this, (+ reg_rn reg_rm)))
                            (armv6m''update_pc pc)
                        )
                        (= op code'LDRSB) #_"LDRSB <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 0 1 1 Rm Rn Rt"
                        (do
                            (aset regs (aget this i'rt) (armv6m''sign_extend this, (cpu''read8 this, (+ reg_rn reg_rm)), 8))
                            (armv6m''update_pc pc)
                        )
                        (= op code'LDRSH) #_"LDRSH <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 1 1 1 Rm Rn Rt"
                        (do
                            (aset regs (aget this i'rt) (armv6m''sign_extend this, (cpu''read16 this, (+ reg_rn reg_rm)), 16))
                            (armv6m''update_pc pc)
                        )
                        (= op code'POP) #_"POP <registers>" #_"1 0 1 1 1 1 0 P register_list"
                        (do
                            (§ ass #_"u32" sp (aget regs reg'SP))

                            (§ for (§ ass #_"s32" i 0) (and (< i REGISTERS) (not (zero? (aget this i'reglist)))) (§ ass i (inc i))
                                (when-not (zero? (bit-and (aget this i'reglist) (<< 1 i)))
                                    (aset regs i (cpu''read32 this, sp))

                                    (§ ass sp (+ sp 4))

                                    (when (= i reg'PC)
                                        (when-not (= (bit-and (aget regs reg'PC) EXC_RETURN) EXC_RETURN)
                                            (armv6m''update_pc (bit-and (aget regs reg'PC) (bit-not 1)))
                                        )
                                        (§ ass pc (aget regs i))
                                    )

                                    (aset this i'reglist (bit-and (aget this i'reglist) (bit-not (<< 1 i))))
                                )
                            )

                            (armv6m''update_sp this, sp)
                            (armv6m''update_pc pc)
                        )
                        (= op code'PUSH) #_"PUSH <registers>" #_"1 0 1 1 0 1 0 M register_list"
                        (do
                            (§ ass #_"u32" sp (aget regs reg'SP))
                            (§ ass #_"u32" addr sp)
                            (§ ass #_"s32" bits_set 0)

                            (§ for (§ ass #_"s32" i 0) (< i REGISTERS) (§ ass i (inc i))
                                (when-not (zero? (bit-and (aget this i'reglist) (<< 1 i)))
                                    (§ ass bits_set (inc bits_set))
                                )
                            )

                            (§ ass addr (- addr (<< bits_set 2)))

                            (§ for (§ ass #_"s32" i 0) (and (< i REGISTERS) (not (zero? (aget this i'reglist)))) (§ ass i (inc i))
                                (when-not (zero? (bit-and (aget this i'reglist) (<< 1 i)))
                                    (cpu''write32 this, addr, (aget regs i))
                                    (§ ass sp (- sp 4))
                                    (§ ass addr (+ addr 4))
                                    (aset this i'reglist (bit-and (aget this i'reglist) (bit-not (<< 1 i))))
                                )
                            )

                            (armv6m''update_sp this, sp)
                            (armv6m''update_pc pc)
                        )
                        (= op code'STR_2) #_"STR <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 0 0 0 Rm Rn Rt"
                        (do
                            (cpu''write32 this, (+ reg_rn reg_rm), (aget regs (aget this i'rt)))
                            (armv6m''update_pc pc)
                        )
                        (= op code'STRB_1) #_"STRB <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 0 1 0 Rm Rn Rt"
                        (do
                            (cpu''write8 this, (+ reg_rn reg_rm), (aget regs (aget this i'rt)))
                            (armv6m''update_pc pc)
                        )
                        (= op code'STRH_1) #_"STRH <Rt>,[<Rn>,<Rm>]" #_"0 1 0 1 0 0 1 Rm Rn Rt"
                        (do
                            (cpu''write16 this, (+ reg_rn reg_rm), (aget regs (aget this i'rt)))
                            (armv6m''update_pc pc)
                        )
                        (= op code'SUBS) #_"SUBS <Rd>,<Rn>,#<imm3>" #_"0 0 0 1 1 1 1 imm3 Rn Rd"
                        (do
                            (armv6m''update_rd this, (armv6m''add_with_carry this, reg_rn, (bit-not (aget this i'imm)), 1, flags'all))
                            (armv6m''update_pc pc)
                        )
                        (= op code'SUBS_2) #_"SUBS <Rd>,<Rn>,<Rm>" #_"0 0 0 1 1 0 1 Rm Rn Rd"
                        (do
                            (armv6m''update_rd this, (armv6m''add_with_carry this, reg_rn, (bit-not reg_rm), 1, flags'all))
                            (armv6m''update_pc pc)
                        )
                    )
                )

                (= inst_group code'IGRP3)
                (let [
                    #_"u16" op (bit-and inst mask'IGRP3)
                ]
                    (cond
                        (= op code'ADD) #_"ADD <Rdn>,<Rm>" #_"0 1 0 0 0 1 0 0 Rm Rdn"
                        (do
                            (armv6m''update_rd this, (+ reg_rn reg_rm))
                            (armv6m''update_pc pc)
                        )
                        (= op code'BKPT) #_"BKPT #<imm8>" #_"1 0 1 1 1 1 1 0 imm8"
                        (do
                            (armv6m''update_pc pc)
                        )
                        (= op code'CMP_2) #_"CMP <Rn>,<Rm> <Rn> and <Rm> not both from R0-R7" #_"0 1 0 0 0 1 0 1 N Rm Rn"
                        (do
                            (armv6m''add_with_carry this, reg_rn, (bit-not reg_rm), 1, flags'all)
                            (armv6m''update_pc pc)
                        )
                        (= op code'MOV) #_"MOV <Rd>,<Rm> Otherwise all versions of the Thumb instruction set." #_"0 1 0 0 0 1 1 0 D Rm Rd"
                        (do
                            (if (= (aget this i'rd) reg'PC)
                                (do
                                    (§ ass pc (bit-and reg_rm (bit-not 1)))
                                )
                                (do
                                    (armv6m''update_rd this, reg_rm)
                                )
                            )
                            (armv6m''update_pc pc)
                        )
                        (= op code'SVC) #_"SVC #<imm8>" #_"1 1 0 1 1 1 1 1 imm8"
                        (do
                            (armv6m''update_pc (armv6m''exception this, pc, 11))
                        )
                        (= op code'UDF) #_"UDF #<imm8>" #_"1 1 0 1 1 1 1 0 imm8"
                        (do
                            (armv6m''update_pc pc)
                        )
                    )
                )

                (= inst_group code'IGRP4)
                (let [
                    #_"u16" op (bit-and inst mask'IGRP4)
                ]
                    (cond
                        (= op code'ADD_2) #_"ADD SP,SP,#<imm7>" #_"1 0 1 1 0 0 0 0 0 imm7"
                        (do
                            (armv6m''update_rd this, (+ reg_rn (<< (aget this i'imm) 2)))
                            (armv6m''update_pc pc)
                        )
                        (= op code'BLX) #_"BLX <Rm>" #_"0 1 0 0 0 1 1 1 1 Rm (0) (0) (0)"
                        (do
                         ;; (aset this i'rd reg'LR)
                            (armv6m''update_rd this, (bit-or pc 1))
                            (armv6m''update_pc (bit-and reg_rm (bit-not 1)))
                        )
                        (= op code'BX) #_"BX <Rm>" #_"0 1 0 0 0 1 1 1 0 Rm (0) (0) (0)"
                        (do
                            (armv6m''update_pc (bit-and reg_rm (bit-not 1)))
                        )
                        (= op code'SUB) #_"SUB SP,SP,#<imm7>" #_"1 0 1 1 0 0 0 0 1 imm7"
                        (do
                            (armv6m''update_rd this, (- reg_rn (<< (aget this i'imm) 2)))
                            (armv6m''update_pc pc)
                        )
                    )
                )

                (= inst_group code'IGRP5)
                (let [
                    #_"u16" op (bit-and inst mask'IGRP5)
                ]
                    (cond
                        (= op code'ADCS) #_"ADCS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 1 0 1 Rm Rdn"
                        (do
                            (armv6m''update_rd this, (armv6m''add_with_carry this, reg_rn, reg_rm, (if (zero? (bit-and (aget this i'apsr) flag'C)) 0 1), flags'all))
                            (armv6m''update_pc pc)
                        )
                        (= op code'ANDS) #_"ANDS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 0 0 0 Rm Rdn"
                        (let [
                            #_"u32" reg_rd (bit-and reg_rn reg_rm)
                        ]
                            (armv6m''update_rd this, reg_rd)
                            (armv6m''update_nz this, reg_rd)
                            (armv6m''update_pc pc)
                        )
                        (= op code'ASRS_1) #_"ASRS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 1 0 0 Rm Rdn"
                        (do
                            (armv6m''update_rd this, (armv6m''arith_shift_right this, reg_rn, reg_rm, flags'NZC))
                            (armv6m''update_pc pc)
                        )
                        (= op code'BICS) #_"BICS <Rdn>,<Rm>" #_"0 1 0 0 0 0 1 1 1 0 Rm Rdn"
                        (let [
                            #_"u32" reg_rd (bit-and reg_rn (bit-not reg_rm))
                        ]
                            (armv6m''update_rd this, reg_rd)
                            (armv6m''update_nz this, reg_rd)
                            (armv6m''update_pc pc)
                        )
                        (= op code'CMN) #_"CMN <Rn>,<Rm>" #_"0 1 0 0 0 0 1 0 1 1 Rm Rn"
                        (do
                            (armv6m''add_with_carry this, reg_rn, reg_rm, 0, flags'all)
                            (armv6m''update_pc pc)
                        )
                        (= op code'CMP_1) #_"CMP <Rn>,<Rm> <Rn> and <Rm> both from R0-R7" #_"0 1 0 0 0 0 1 0 1 0 Rm Rn"
                        (do
                            (armv6m''add_with_carry this, reg_rn, (bit-not reg_rm), 1, flags'all)
                            (armv6m''update_pc pc)
                        )
                        (= op code'EORS) #_"EORS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 0 0 1 Rm Rdn"
                        (let [
                            #_"u32" reg_rd (bit-xor reg_rn reg_rm)
                        ]
                            (armv6m''update_rd this, reg_rd)
                            (armv6m''update_nz this, reg_rd)
                            (armv6m''update_pc pc)
                        )
                        (= op code'LSLS_1) #_"LSLS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 0 1 0 Rm Rdn"
                        (do
                            (if (zero? reg_rm)
                                (do
                                    (armv6m''update_rd this, reg_rn)
                                    (armv6m''update_nz this, reg_rn)
                                )
                                (do
                                    (armv6m''update_rd this, (armv6m''shift_left this, reg_rn, reg_rm, flags'NZC))
                                )
                            )
                            (armv6m''update_pc pc)
                        )
                        (= op code'LSRS_1) #_"LSRS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 0 1 1 Rm Rdn"
                        (do
                            (armv6m''update_rd this, (armv6m''shift_right this, reg_rn, (bit-and reg_rm 0xff), flags'NZC))
                            (armv6m''update_pc pc)
                        )
                        (= op code'MULS) #_"MULS <Rdm>,<Rn>,<Rdm>" #_"0 1 0 0 0 0 1 1 0 1 Rn Rdm"
                        (let [
                            #_"u32" reg_rd (* reg_rn reg_rm)
                        ]
                            (armv6m''update_rd this, reg_rd)
                            (armv6m''update_nz this, reg_rd)
                            (armv6m''update_pc pc)
                        )
                        (= op code'MVNS) #_"MVNS <Rd>,<Rm>" #_"0 1 0 0 0 0 1 1 1 1 Rm Rd"
                        (let [
                            #_"u32" reg_rd (bit-not reg_rm)
                        ]
                            (armv6m''update_rd this, reg_rd)
                            (armv6m''update_nz this, reg_rd)
                            (armv6m''update_pc pc)
                        )
                        (= op code'ORRS) #_"ORRS <Rdn>,<Rm>" #_"0 1 0 0 0 0 1 1 0 0 Rm Rdn"
                        (let [
                            #_"u32" reg_rd (bit-or reg_rn reg_rm)
                        ]
                            (armv6m''update_rd this, reg_rd)
                            (armv6m''update_nz this, reg_rd)
                            (armv6m''update_pc pc)
                        )
                        (= op code'REV) #_"REV <Rd>,<Rm>" #_"1 0 1 1 1 0 1 0 0 0 Rm Rd"
                        (do
                            (armv6m''update_rd this, (bit-or (<< (bit-and (>>> reg_rm 0) 0xff) 24) (<< (bit-and (>>> reg_rm 8) 0xff) 16) (<< (bit-and (>>> reg_rm 16) 0xff) 8) (<< (bit-and (>>> reg_rm 24) 0xff) 0)))
                            (armv6m''update_pc pc)
                        )
                        (= op code'REV16) #_"REV16 <Rd>,<Rm>" #_"1 0 1 1 1 0 1 0 0 1 Rm Rd"
                        (do
                            (armv6m''update_rd this, (bit-or (<< (bit-and (>>> reg_rm 0) 0xff) 8) (<< (bit-and (>>> reg_rm 8) 0xff) 0) (<< (bit-and (>>> reg_rm 16) 0xff) 24) (<< (bit-and (>>> reg_rm 24) 0xff) 16)))
                            (armv6m''update_pc pc)
                        )
                        (= op code'REVSH) #_"REVSH <Rd>,<Rm>" #_"1 0 1 1 1 0 1 0 1 1 Rm Rd"
                        (do
                            (armv6m''update_rd this, (armv6m''sign_extend this, (bit-or (<< (bit-and (>>> reg_rm 0) 0xff) 8) (<< (bit-and (>>> reg_rm 8) 0xff) 0)), 16))
                            (armv6m''update_pc pc)
                        )
                        (= op code'RORS) #_"RORS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 1 1 1 Rm Rdn"
                        (do
                            (armv6m''update_rd this, (armv6m''rotate_right this, reg_rn, (bit-and reg_rm 0xff), flags'NZC))
                            (armv6m''update_pc pc)
                        )
                        (= op code'RSBS) #_"RSBS <Rd>,<Rn>,#0" #_"0 1 0 0 0 0 1 0 0 1 Rn Rd"
                        (do
                            (armv6m''update_rd this, (armv6m''add_with_carry this, (bit-not reg_rn), 0, 1, flags'all))
                            (armv6m''update_pc pc)
                        )
                        (= op code'SBCS) #_"SBCS <Rdn>,<Rm>" #_"0 1 0 0 0 0 0 1 1 0 Rm Rdn"
                        (do
                            (armv6m''update_rd this, (armv6m''add_with_carry this, reg_rn, (bit-not reg_rm), (if (zero? (bit-and (aget this i'apsr) flag'C)) 0 1), flags'all))
                            (armv6m''update_pc pc)
                        )
                        (= op code'SXTB) #_"SXTB <Rd>,<Rm>" #_"1 0 1 1 1 0 0 0 0 1 Rm Rd"
                        (let [
                            #_"u32" reg_rd (bit-and reg_rm 0xff)
                            reg_rd (if-not (zero? (bit-and reg_rd 0x80)) (bit-or reg_rd (<< (bit-not 0) 8)) reg_rd)
                        ]
                            (armv6m''update_rd this, reg_rd)
                            (armv6m''update_pc pc)
                        )
                        (= op code'SXTH) #_"SXTH <Rd>,<Rm>" #_"1 0 1 1 1 0 0 0 0 0 Rm Rd"
                        (let [
                            #_"u32" reg_rd (bit-and reg_rm 0xffff)
                            reg_rd (if-not (zero? (bit-and reg_rd 0x8000)) (bit-or reg_rd (<< (bit-not 0) 16)) reg_rd)
                        ]
                            (armv6m''update_rd this, reg_rd)
                            (armv6m''update_pc pc)
                        )
                        (= op code'TST) #_"TST <Rn>,<Rm>" #_"0 0 0 1 0 0 1 0 0 0 Rm Rn"
                        (do
                            (armv6m''update_nz this, (bit-and reg_rn reg_rm))
                            (armv6m''update_pc pc)
                        )
                        (= op code'UXTB) #_"UXTB <Rd>,<Rm>" #_"1 0 1 1 1 0 0 0 1 1 Rm Rd"
                        (do
                            (armv6m''update_rd this, (bit-and reg_rm 0xff))
                            (armv6m''update_pc pc)
                        )
                        (= op code'UXTH) #_"UXTH <Rd>,<Rm>" #_"1 0 1 1 1 0 0 0 1 0 Rm Rd"
                        (do
                            (armv6m''update_rd this, (bit-and reg_rm 0xffff))
                            (armv6m''update_pc pc)
                        )
                    )
                )

                (= inst_group code'IGRP6)
                (let [
                    #_"u16" op (bit-and inst mask'IGRP6)
                ]
                    (cond
                        (= op code'MRS) #_"MRS <Rd>,<spec_reg>" #_"1 1 1 0 1 0 1 1 1 1 1 (0) (1) (1) (1) (1) 1 0 (0) 0 Rd SYSm"
                        (do
                            (§ ass #_"u32" sysm (bit-and (>>> inst2 0) 0xff))
                            (aset this i'rd (bit-and (>>> inst2 8) 0xf))

                            (§ ass pc (+ pc 2))

                            (§ switch (bit-and (>>> sysm 3) 0x1f)
                                (§ case 0)
                                (do
                                    (§ ass #_"u32" val 0)

                                    (when-not (zero? (bit-and sysm 0x1))
                                        (§ ass val (bit-or val (bit-and (aget this i'ipsr) 0x1ff)))
                                    )

                                    (when (zero? (bit-and sysm 0x4))
                                        (§ ass val (bit-or val (bit-and (aget this i'apsr) 0xf8000000)))
                                    )

                                    (§ ass val (bit-or val (aget this i'ipsr)))
                                    (§ ass val (bit-or val (aget this i'epsr)))

                                    (armv6m''update_rd this, val)
                                    (§ break)
                                )
                                (§ case 1)
                                (do
                                    (§ switch (bit-and sysm 0x7)
                                        (§ case 0)
                                        (do
                                            (armv6m''update_rd this, (aget this i'msp))
                                            (§ break)
                                        )
                                        (§ case 1)
                                        (do
                                            (armv6m''update_rd this, (aget this i'psp))
                                            (§ break)
                                        )
                                    )
                                    (§ break)
                                )
                                (§ case 2)
                                (do
                                    (§ switch (bit-and sysm 0x7)
                                        (§ case 0)
                                        (do
                                            (armv6m''update_rd this, (bit-and (aget this i'primask) PRIMASK_PM))
                                            (§ break)
                                        )
                                        (§ case 4)
                                        (do
                                            (armv6m''update_rd this, (bit-and (aget this i'control) CONTROL_MASK))
                                            (§ break)
                                        )
                                    )
                                    (§ break)
                                )
                            )
                            (armv6m''update_pc pc)
                        )
                        (= op code'MSR) #_"MSR <spec_reg>,<Rn>" #_"1 1 1 0 1 0 1 1 1 0 0 (0) Rn 1 0 (0) 0 (1) (0) (0) (0) SYSm"
                        (do
                            (§ ass #_"u32" sysm (bit-and (>>> inst2 0) 0xff))

                            (§ ass pc (+ pc 2))

                            (§ switch (bit-and (>>> sysm 3) 0x1f)
                                (§ case 0)
                                (do
                                    (when (zero? (bit-and sysm 0x4))
                                        (aset this i'apsr (bit-and reg_rn 0xf8000000))
                                    )
                                    (§ break)
                                )
                                (§ case 1)
                                (do
                                    ;; TODO: Only if privileged...
                                    (§ switch (bit-and sysm 0x7)
                                        (§ case 0)
                                        (do
                                            (aset this i'msp reg_rn)
                                            (§ break)
                                        )
                                        (§ case 1)
                                        (do
                                            (aset this i'psp reg_rn)
                                            (§ break)
                                        )
                                    )
                                    (§ break)
                                )
                                (§ case 2)
                                (do
                                    ;; TODO: Only if privileged...
                                    (§ switch (bit-and sysm 0x7)
                                        (§ case 0)
                                        (do
                                            (aset this i'primask (bit-and reg_rn PRIMASK_PM))
                                            (§ break)
                                        )
                                        (§ case 4)
                                        (do
                                            (when-not (aget this i'handler?)
                                                (aset this i'control (bit-and reg_rn CONTROL_MASK))

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
                            (armv6m''update_pc pc)
                        )
                        (= op code'CPS) #_"CPS<effect> i" #_"1 0 1 1 0 1 1 0 0 1 1 im (0) (0) (1) (0)"
                        (do
                            ;; TODO: Only if privileged...
                            (if (zero? (aget this i'imm))
                                (aset this i'primask (bit-and (aget this i'primask) (bit-not PRIMASK_PM))) #_"Enable"
                                (aset this i'primask (bit-or  (aget this i'primask)          PRIMASK_PM))  #_"Disable"
                            )
                            (armv6m''update_pc pc)
                        )
                    )
                )

                (= inst_group code'IGRP7)
                (let [
                    #_"u16" op (bit-and inst mask'IGRP7)
                ]
                    (cond
                        (or
                            (= op code'DMB)   #_"DMB #<option>"  #_"1 1 1 0 1 0 1 1 1 0 1 1 (1) (1) (1) (1) 1 0 (0) 0 (1) (1) (1) (1) 0 1 0 1 option"
                            (= op code'DSB)   #_"DSB #<option>"  #_"1 1 1 0 1 0 1 1 1 0 1 1 (1) (1) (1) (1) 1 0 (0) 0 (1) (1) (1) (1) 0 1 0 0 option"
                            (= op code'ISB)   #_"ISB #<option>"  #_"1 1 1 0 1 0 1 1 1 0 1 1 (1) (1) (1) (1) 1 0 (0) 0 (1) (1) (1) (1) 0 1 1 0 option"
                            (= op code'UDF_W) #_"UDF_W #<imm16>" #_"1 1 1 1 0 1 1 1 1 1 1 1 imm4 1 0 1 0 imm12"
                        )
                        (do
                            (armv6m''update_pc (+ pc 2))
                        )
                    )
                )

                (= inst_group code'IGRP8)
                (let [
                    #_"u16" op (bit-and inst mask'IGRP8)
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
                            (armv6m''update_pc pc)
                        )
                    )
                )
            )
        )
        nil
    )
)
