(ns beagle.armv6m
    (:refer-clojure :only [& * + - < << <= >> >>> | aget and aset bit-not byte-array cons defmacro defn first next object-array or when])
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
        (ß (#_"u16")
            (|
                (<< (ß (#_"u32")(ram''read8 this, (+ addr 0))) 0)
                (<< (ß (#_"u32")(ram''read8 this, (+ addr 1))) 8)
            )
        )
    )

    (defn #_"u32" ram''read32 [#_"ram" this, #_"u32" addr]
        (ß (#_"u32")
            (|
                (<< (ß (#_"u32")(ram''read8 this, (+ addr 0))) 0)
                (<< (ß (#_"u32")(ram''read8 this, (+ addr 1))) 8)
                (<< (ß (#_"u32")(ram''read8 this, (+ addr 2))) 16)
                (<< (ß (#_"u32")(ram''read8 this, (+ addr 3))) 24)
            )
        )
    )
)

(about #_"cpu"

    (def reg'SP    13)
    (def reg'LR    14)
    (def reg'PC    15)
    (def REGISTERS 16)

    (def shift'APSR_N 31)
    (def shift'APSR_Z 30)
    (def shift'APSR_C 29)
    (def shift'APSR_V 28)

    (def APSR_N (<< 1 shift'APSR_N))
    (def APSR_Z (<< 1 shift'APSR_Z))
    (def APSR_C (<< 1 shift'APSR_C))
    (def APSR_V (<< 1 shift'APSR_V))

    (def ALL_FLAGS (| APSR_N APSR_Z APSR_C APSR_V))
    (def FLAGS_NZC (| APSR_N APSR_Z APSR_C))

    (def PRIMASK_PM (<< 1 0))

    (def CONTROL_NPRIV (<< 1 0))
    (def CONTROL_SPSEL (<< 1 1))
    (def CONTROL_MASK  (| CONTROL_NPRIV CONTROL_SPSEL))

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

                ;; Fetch SP & boot PC from vector table
                (aset regfile reg'SP    (cpu''read32 this,    (ram'base ram)))
                (aset regfile reg'PC (& (cpu''read32 this, (+ (ram'base ram) 4)) (bit-not 1)))

                ;; Start in thread mode with main stack selected
                (aset this i'msp (aget regfile reg'SP))

                this
            )
        )
    )

    (defn #_"void" cpu''write8  [#_"cpu" this, #_"u32" addr, #_"u8"  data] (ram''write8  (aget this i'ram),    addr,              data) nil)
    (defn #_"void" cpu''write16 [#_"cpu" this, #_"u32" addr, #_"u16" data] (ram''write16 (aget this i'ram), (& addr (bit-not 1)), data) nil)
    (defn #_"void" cpu''write32 [#_"cpu" this, #_"u32" addr, #_"u32" data] (ram''write32 (aget this i'ram), (& addr (bit-not 3)), data) nil)

    (defn #_"u8"  cpu''read8  [#_"cpu" this, #_"u32" addr] (ram''read8  (aget this i'ram),    addr))
    (defn #_"u16" cpu''read16 [#_"cpu" this, #_"u32" addr] (ram''read16 (aget this i'ram), (& addr (bit-not 1))))
    (defn #_"u32" cpu''read32 [#_"cpu" this, #_"u32" addr] (ram''read32 (aget this i'ram), (& addr (bit-not 3))))

    (defn #_"cpu" cpu''step [#_"cpu" this]
        (when (ß ((aget this i'regfile)[reg'PC] & EXC_RETURN) == EXC_RETURN)
            (ß armv6m_exc_return(this, (aget this i'regfile)[reg'PC]))
        )

        (ß #_"u16" inst = armv6m_read_inst(this, (aget this i'regfile)[reg'PC]))

        (ß #_"u16" inst2)
        (if (ß armv6m_decode(this, inst))
            (ß inst2 = armv6m_read_inst(this, (aget this i'regfile)[reg'PC] + 2))
            (ß inst2 = 0)
        )

        (ß armv6m_execute(this, inst, inst2))
        this
    )

    (defn #_"u16" armv6m_read_inst [#_"cpu" this, #_"u32" addr]
        (if (ß addr & 0x2)
            (§ return (cpu''read32(this, addr) >>> 16) & 0xffff)
            (§ return (cpu''read32(this, addr) >>> 0) & 0xffff)
        )
    )

    (defn #_"void" armv6m_update_sp [#_"cpu" this, #_"u32" sp]
        (ß (aget this i'regfile)[reg'SP] = sp)

        (if (ß ((aget this i'control) & CONTROL_SPSEL) && !(aget this i'handler?))
            (ß (aget this i'psp) = sp)
            (ß (aget this i'msp) = sp)
        )
        nil
    )

    (defn #_"void" armv6m_update_n_z_flags [#_"cpu" this, #_"u32" rd]
        ;; Zero
        (if (ß rd == 0)
            (ß (aget this i'apsr) |= APSR_Z)
            (ß (aget this i'apsr) &= (bit-not APSR_Z))
        )

        ;; Negative
        (if (ß rd & 0x80000000)
            (ß (aget this i'apsr) |= APSR_N)
            (ß (aget this i'apsr) &= (bit-not APSR_N))
        )
        nil
    )

    (defn #_"u32" armv6m_add_with_carry [#_"cpu" this, #_"u32" rn, #_"u32" rm, #_"u32" carry_in, #_"u32" mask]
        (ß #_"u32" res = rn + rm + carry_in)

        ;; Zero
        (when (ß mask & APSR_Z)
            (if (ß (res & 0xffffffff) == 0)
                (ß (aget this i'apsr) |= APSR_Z)
                (ß (aget this i'apsr) &= (bit-not APSR_Z))
            )
        )

        ;; Negative
        (when (ß mask & APSR_N)
            (if (ß res & 0x80000000)
                (ß (aget this i'apsr) |= APSR_N)
                (ß (aget this i'apsr) &= (bit-not APSR_N))
            )
        )

        ;; Carry
        (when (ß mask & APSR_C)
            (ß #_"u64" unsigned_sum = (#_"u64")rn + (#_"u64")rm + carry_in)
            (if (ß unsigned_sum == (#_"u64")res)
                (ß (aget this i'apsr) &= (bit-not APSR_C))
                (ß (aget this i'apsr) |= APSR_C)
            )
        )

        ;; Overflow
        (when (ß mask & APSR_V)
            (ß int64_t signed_sum = (int64_t)(int32_t)rn + (int64_t)(int32_t)rm + carry_in)
            (if (ß signed_sum == (int64_t)(int32_t)res)
                (ß (aget this i'apsr) &= (bit-not APSR_V))
                (ß (aget this i'apsr) |= APSR_V)
            )
        )

        (§ return (#_"u32")res)
    )

    (defn #_"u32" armv6m_shift_left [#_"cpu" this, #_"u32" val, #_"u32" shift, #_"u32" mask]
        (ß #_"u64" res = val)
        (ß res <<= shift)

        ;; Carry Out (res[32])
        (when (ß mask & APSR_C)
            (if (ß res & ((#_"u64")1 << 32))
                (ß (aget this i'apsr) |= APSR_C)
                (ß (aget this i'apsr) &= (bit-not APSR_C))
            )
        )

        ;; Zero
        (if (ß (res & 0xffffffff) == 0)
            (ß (aget this i'apsr) |= APSR_Z)
            (ß (aget this i'apsr) &= (bit-not APSR_Z))
        )

        ;; Negative
        (if (ß res & 0x80000000)
            (ß (aget this i'apsr) |= APSR_N)
            (ß (aget this i'apsr) &= (bit-not APSR_N))
        )

        (§ return (#_"u32")res)
    )

    (defn #_"u32" armv6m_shift_right [#_"cpu" this, #_"u32" val, #_"u32" shift, #_"u32" mask]
        (ß #_"u32" res = (32 <= shift) ? 0 : val)

        ;; Carry Out (val[shift-1])
        (when (ß (mask & APSR_C) && (shift > 0))
            ;; Last lost bit shifted right
            (if (ß (val & (1 << (shift - 1))) && (shift <= 32))
                (ß (aget this i'apsr) |= APSR_C)
                (ß (aget this i'apsr) &= (bit-not APSR_C))
            )
        )

        (ß res = res >>> shift)

        ;; Zero
        (if (ß (res & 0xffffffff) == 0)
            (ß (aget this i'apsr) |= APSR_Z)
            (ß (aget this i'apsr) &= (bit-not APSR_Z))
        )

        ;; Negative
        (if (ß res & 0x80000000)
            (ß (aget this i'apsr) |= APSR_N)
            (ß (aget this i'apsr) &= (bit-not APSR_N))
        )

        (§ return res)
    )

    (defn #_"u32" armv6m_arith_shift_right [#_"cpu" this, #_"u32" val, #_"u32" shift, #_"u32" mask]
        (ß signed #_"s32" res = val)

        ;; Carry Out (val[shift-1])
        (when (ß (mask & APSR_C) && (shift > 0))
            ;; Last lost bit shifted right
            (if (ß val & (1 << (shift - 1)))
                (ß (aget this i'apsr) |= APSR_C)
                (ß (aget this i'apsr) &= (bit-not APSR_C))
            )
        )

        (ß res = res >> shift)

        ;; Zero
        (if (ß (res & 0xffffffff) == 0)
            (ß (aget this i'apsr) |= APSR_Z)
            (ß (aget this i'apsr) &= (bit-not APSR_Z))
        )

        ;; Negative
        (if (ß res & 0x80000000)
            (ß (aget this i'apsr) |= APSR_N)
            (ß (aget this i'apsr) &= (bit-not APSR_N))
        )

        (§ return res)
    )

    (defn #_"u32" armv6m_rotate_right [#_"cpu" this, #_"u32" val, #_"u32" shift, #_"u32" mask]
        (ß #_"u32" res)

        (if (ß shift == 0)
            (ß res = val)
            (do
                (ß shift &= 0x1f)

                (ß res = val >>> shift)
                (ß res |= (val << (32 - shift)))
            )
        )

        ;; Carry out
        (if (ß res & 0x80000000)
            (ß (aget this i'apsr) |= APSR_C)
            (ß (aget this i'apsr) &= (bit-not APSR_C))
        )

        ;; Zero
        (if (ß (res & 0xffffffff) == 0)
            (ß (aget this i'apsr) |= APSR_Z)
            (ß (aget this i'apsr) &= (bit-not APSR_Z))
        )

        ;; Negative
        (if (ß res & 0x80000000)
            (ß (aget this i'apsr) |= APSR_N)
            (ß (aget this i'apsr) &= (bit-not APSR_N))
        )

        (§ return res)
    )

    (defn #_"u32" armv6m_sign_extend [#_"cpu" this, #_"u32" val, #_"s32" offset]
        (if (ß val & (1 << (offset - 1)))
            (ß val |= (bit-not 0) << offset)
            (ß val &= (bit-not ((bit-not 0) << offset)))
        )

        (§ return val)
    )

    (defn #_"u32" armv6m_exception [#_"cpu" this, #_"u32" pc, #_"u32" exception]
        (ß #_"u32" sp)

        ;; Retrieve shadow stack pointer (depending on mode)
        (if (ß ((aget this i'control) & CONTROL_SPSEL) && !(aget this i'handler?))
            (ß sp = (aget this i'psp))
            (ß sp = (aget this i'msp))
        )

        ;; Push frame onto current stack
        (ß sp = sp - 4)
        (ß cpu''write32(this, sp, (aget this i'apsr)))
        (ß sp = sp - 4)
        (ß cpu''write32(this, sp, (aget this i'regfile)[reg'PC]))
        (ß sp = sp - 4)
        (ß cpu''write32(this, sp, (aget this i'regfile)[reg'LR]))
        (ß sp = sp - 4)
        (ß cpu''write32(this, sp, (aget this i'regfile)[12]))
        (ß sp = sp - 4)
        (ß cpu''write32(this, sp, (aget this i'regfile)[3]))
        (ß sp = sp - 4)
        (ß cpu''write32(this, sp, (aget this i'regfile)[2]))
        (ß sp = sp - 4)
        (ß cpu''write32(this, sp, (aget this i'regfile)[1]))
        (ß sp = sp - 4)
        (ß cpu''write32(this, sp, (aget this i'regfile)[0]))
        (ß (aget this i'regfile)[reg'SP] = sp)

        ;; Record exception
        (ß (aget this i'ipsr) = exception & 0x3f)

        ;; Fetch exception vector address into PC
        (ß (aget this i'regfile)[reg'PC] = cpu''read32(this, (ram'base (aget this i'ram)) + (exception * 4)) & (bit-not 1))

        (if (ß (aget this i'handler?))
            (do
                ;; LR = Return to handler mode (recursive interrupt?)
                (ß (aget this i'regfile)[reg'LR] = 0xfffffff1)
            )
            (if (ß ((aget this i'control) & CONTROL_SPSEL) == 0)
                (do
                    ;; LR = Return to thread mode (with main stack)
                    (ß (aget this i'regfile)[reg'LR] = 0xfffffff9)
                )
                (do
                    ;; LR = Return to thread mode (with process stack)
                    (ß (aget this i'regfile)[reg'LR] = 0xfffffffd)
                )
            )
        )

        ;; Swap to handler mode
        (ß (aget this i'handler?) = true)

        ;; Current stack is now main
        (ß (aget this i'control) &= (bit-not CONTROL_SPSEL))

        (§ return (aget this i'regfile)[reg'PC])
    )

    (defn #_"void" armv6m_exc_return [#_"cpu" this, #_"u32" pc]
        (when (ß !(aget this i'handler?))
            (§ return nil)
        )

        (when (ß (pc & EXC_RETURN) == EXC_RETURN)
            ;; TODO: Should be 0x1f...
            (§ switch (pc & 0xf)
                (§ case 0x1)
                (§
                    (ß (aget this i'handler?) = true)
                    (ß (aget this i'control) &= (bit-not CONTROL_SPSEL))
                    (§ break)
                )
                (§ case 0x9)
                (§
                    (ß (aget this i'handler?) = false)
                    (ß (aget this i'control) &= (bit-not CONTROL_SPSEL))
                    (§ break)
                )
                (§ case 0xd)
                (§
                    (ß (aget this i'handler?) = false)
                    (ß (aget this i'control) |= CONTROL_SPSEL)
                    (§ break)
                )
                (§ default)
                (§
                    (ß assert(!"Not handled"))
                    (§ break)
                )
            )

            (ß #_"u32" sp = (aget this i'regfile)[reg'SP])
            (ß (aget this i'regfile)[0] = cpu''read32(this, sp))
            (ß sp = sp + 4)
            (ß (aget this i'regfile)[1] = cpu''read32(this, sp))
            (ß sp = sp + 4)
            (ß (aget this i'regfile)[2] = cpu''read32(this, sp))
            (ß sp = sp + 4)
            (ß (aget this i'regfile)[3] = cpu''read32(this, sp))
            (ß sp = sp + 4)
            (ß (aget this i'regfile)[12] = cpu''read32(this, sp))
            (ß sp = sp + 4)
            (ß (aget this i'regfile)[reg'LR] = cpu''read32(this, sp))
            (ß sp = sp + 4)
            (ß (aget this i'regfile)[reg'PC] = cpu''read32(this, sp))
            (ß sp = sp + 4)
            (ß (aget this i'apsr) = cpu''read32(this, sp))
            (ß sp = sp + 4)
            (ß armv6m_update_sp(this, sp))
        )
        nil
    )

    (defn #_"bool" armv6m_decode [#_"cpu" this, #_"u16" inst]
        (ß #_"bool" res = false)
        (ß #_"bool" v_decoded = false)

        (ß (aget this i'rd) = 0)
        (ß (aget this i'rt) = 0)
        (ß (aget this i'rm) = 0)
        (ß (aget this i'rn) = 0)
        (ß (aget this i'imm) = 0)
        (ß (aget this i'cond) = 0)
        (ß (aget this i'reglist) = 0)

        ;; Group 0?
        (when (ß !v_decoded)
            (ß v_decoded = true)
            (ß (aget this i'inst_group) = code'IGRP0)
            (§ switch (inst & mask'IGRP0)
                #_"BCC <label>"
                #_"1 1 0 1 cond imm8"
                (§ case code'BCC)
                (§
                    (ß (aget this i'cond) = (inst >>> 8) & 0x0f)
                    (ß (aget this i'imm) = (inst >>> 0) & 0xff)
                    (§ break)
                )
                (§ default)
                (§
                    (ß v_decoded = false)
                    (§ break)
                )
            )
        )

        ;; Group 1?
        (when (ß !v_decoded)
            (ß v_decoded = true)
            (ß (aget this i'inst_group) = code'IGRP1)
            (§ switch (inst & mask'IGRP1)
                #_"ADDS <Rdn>,#<imm8>"
                #_"0 0 1 1 0 Rdn imm8"
                (§ case code'ADDS_1)
                #_"SUBS <Rdn>,#<imm8>"
                #_"0 0 1 11 Rdn imm8"
                (§ case code'SUBS_1)
                (§
                    (ß (aget this i'rd) = (inst >>> 8) & 0x7)
                    (ß (aget this i'rn) = (aget this i'rd))
                    (ß (aget this i'imm) = (inst >>> 0) & 0xff)
                    (§ break)
                )

                #_"ADR <Rd>,<label>"
                #_"1 0 1 0 0 Rd imm8"
                (§ case code'ADR)
                #_"MOVS <Rd>,#<imm8>"
                #_"0 0 1 0 0 Rd imm8"
                (§ case code'MOVS)
                (§
                    (ß (aget this i'rd) = (inst >>> 8) & 0x7)
                    (ß (aget this i'imm) = (inst >>> 0) & 0xff)
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
                    (ß (aget this i'imm) = (inst >>> 6) & 0x1f)
                    (ß (aget this i'rm) = (inst >>> 3) & 0x7)
                    (ß (aget this i'rd) = (inst >>> 0) & 0x7)
                    (§ break)
                )

                #_"B <label>"
                #_"1 1 1 0 0 imm11"
                (§ case code'B)
                (§
                    (ß (aget this i'imm) = (inst >>> 0) & 0x7ff)
                    (§ break)
                )

                #_"BL <label>"
                #_"1 1 1 01 S imm10 1 1 J1 1 J2 imm11"
                (§ case code'BL)
                (§
                    ;; 32-bit instruction
                    (ß res = true)
                    (ß (aget this i'imm) = (inst >>> 0) & 0x7ff)
                    (ß (aget this i'rd) = reg'LR)

                    ;; TODO: Clean this up
                    ;; Check next instruction to work out if this is a BL or MSR
                    (when (ß (armv6m_read_inst(this, (aget this i'regfile)[reg'PC] + 2) & 0xc000) != 0xc000)
                        (ß v_decoded = false)
                    )
                    (§ break)
                )

                #_"CMP <Rn>,#<imm8>"
                #_"0 0 1 0 1 Rn imm8"
                (§ case code'CMP)
                (§
                    (ß (aget this i'rn) = (inst >>> 8) & 0x7)
                    (ß (aget this i'imm) = (inst >>> 0) & 0xff)
                    (§ break)
                )

                #_"LDM <Rn>!,<registers> <Rn> not included in <registers>"
                #_"1 1 0 0 1 Rn register_list"
                #_"LDM <Rn>,<registers> <Rn> included in <registers>"
                #_"1 1 0 0 1 Rn register_list"
             ;; case code'LDM_1:
                (§ case code'LDM)
                #_"STM <Rn>!,<registers>"
                #_"1 1 0 0 0 Rn register_list"
                (§ case code'STM)
                (§
                    (ß (aget this i'rn) = (inst >>> 8) & 0x7)
                    (ß (aget this i'rd) = (aget this i'rn))
                    (ß (aget this i'reglist) = (inst >>> 0) & 0xff)
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
                    (ß (aget this i'imm) = (inst >>> 6) & 0x1f)
                    (ß (aget this i'rn) = (inst >>> 3) & 0x7)
                    (ß (aget this i'rt) = (inst >>> 0) & 0x7)
                    (ß (aget this i'rd) = (aget this i'rt))
                    (§ break)
                )

                #_"LDR <Rt>,<label>"
                #_"0 1 0 0 1 Rt imm8"
                (§ case code'LDR_2)
                (§
                    (ß (aget this i'rt) = (inst >>> 8) & 0x7)
                    (ß (aget this i'rd) = (aget this i'rt))
                    (ß (aget this i'imm) = (inst >>> 0) & 0xff)
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
                    (ß (aget this i'rt) = (inst >>> 8) & 0x7)
                    (ß (aget this i'rn) = reg'SP)
                    (ß (aget this i'rd) = (aget this i'rt))
                    (ß (aget this i'imm) = (inst >>> 0) & 0xff)
                    (§ break)
                )

                (§ default)
                (§
                    (ß v_decoded = false)
                    (§ break)
                )
            )
        )

        ;; Group 2?
        (when (ß !v_decoded)
            (ß v_decoded = true)
            (ß (aget this i'inst_group) = code'IGRP2)
            (§ switch (inst & mask'IGRP2)
                #_"ADDS <Rd>,<Rn>,#<imm3>"
                #_"0 0 0 1 1 1 0 imm3 Rn Rd"
                (§ case code'ADDS)
                #_"SUBS <Rd>,<Rn>,#<imm3>"
                #_"0 0 0 11 1 1 imm3 Rn Rd"
                (§ case code'SUBS)
                (§
                    (ß (aget this i'imm) = (inst >>> 6) & 0x7)
                    (ß (aget this i'rn) = (inst >>> 3) & 0x7)
                    (ß (aget this i'rd) = (inst >>> 0) & 0x7)
                    (§ break)
                )

                #_"ADDS <Rd>,<Rn>,<Rm>"
                #_"0 0 0 1 1 0 0 Rm Rn Rd"
                (§ case code'ADDS_2)
                #_"SUBS <Rd>,<Rn>,<Rm>"
                #_"0 0 0 11 0 1 Rm Rn Rd"
                (§ case code'SUBS_2)
                (§
                    (ß (aget this i'rm) = (inst >>> 6) & 0x7)
                    (ß (aget this i'rn) = (inst >>> 3) & 0x7)
                    (ß (aget this i'rd) = (inst >>> 0) & 0x7)
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
                    (ß (aget this i'rm) = (inst >>> 6) & 0x7)
                    (ß (aget this i'rn) = (inst >>> 3) & 0x7)
                    (ß (aget this i'rt) = (inst >>> 0) & 0x7)
                    (ß (aget this i'rd) = (aget this i'rt))
                    (§ break)
                )

                #_"POP <registers>"
                #_"1 0 1 1 1 1 0 P register_list"
                (§ case code'POP)
                (§
                    (ß (aget this i'reglist) = (inst >>> 0) & 0xff)
                    (when (ß inst & (1 << 8))
                        (ß (aget this i'reglist) |= (1 << reg'PC))
                    )
                    (§ break)
                )

                #_"PUSH <registers>"
                #_"1 0 1 1 0 1 0 M register_list"
                (§ case code'PUSH)
                (§
                    (ß (aget this i'reglist) = (inst >>> 0) & 0xff)
                    (when (ß inst & (1 << 8))
                        (ß (aget this i'reglist) |= (1 << reg'LR))
                    )
                    (§ break)
                )

                (§ default)
                (§
                    (ß v_decoded = false)
                    (§ break)
                )
            )
        )

        ;; Group 3?
        (when (ß !v_decoded)
            (ß v_decoded = true)
            (ß (aget this i'inst_group) = code'IGRP3)
            (§ switch (inst & mask'IGRP3)
                #_"ADD <Rdn>,<Rm>"
                #_"0 1 0 0 0 1 0 0 Rm Rdn"
                (§ case code'ADD)
                (§
                    (ß (aget this i'rm) = (inst >>> 3) & 0xf)
                    (ß (aget this i'rd) = (inst >>> 0) & 0x7)
                    (ß (aget this i'rd) |= (inst >>> 4) & 0x8)
                    (ß (aget this i'rn) = (aget this i'rd))
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
                    (ß (aget this i'imm) = (inst >>> 0) & 0xff)
                    (§ break)
                )

                #_"CMP <Rn>,<Rm> <Rn> and <Rm> not both from R0-R7"
                #_"0 1 0 0 0 1 0 1 N Rm Rn"
                (§ case code'CMP_2)
                (§
                    (ß (aget this i'rm) = (inst >>> 3) & 0xf)
                    (ß (aget this i'rn) = (inst >>> 0) & 0x7)
                    (ß (aget this i'rn) |= (inst >>> 4) & 0x8)
                    (§ break)
                )

                #_"MOV <Rd>,<Rm> Otherwise all versions of the Thumb instruction set."
                #_"0 1 0 0 0 1 1 0 D Rm Rd"
                (§ case code'MOV)
                (§
                    (ß (aget this i'rm) = (inst >>> 3) & 0xf)
                    (ß (aget this i'rd) = (inst >>> 0) & 0x7)
                    (ß (aget this i'rd) |= (inst >>> 4) & 0x8)
                    (§ break)
                )

                (§ default)
                (§
                    (ß v_decoded = false)
                    (§ break)
                )
            )
        )

        ;; Group 4?
        (when (ß !v_decoded)
            (ß v_decoded = true)
            (ß (aget this i'inst_group) = code'IGRP4)
            (§ switch (inst & mask'IGRP4)
                #_"ADD SP,SP,#<imm7>"
                #_"1 0 1 1 0 0 0 0 0 imm7"
                (§ case code'ADD_2)
                #_"SUB SP,SP,#<imm7>"
                #_"1 0 1 1 000 0 1 imm7"
                (§ case code'SUB)
                (§
                    (ß (aget this i'rn) = reg'SP)
                    (ß (aget this i'rd) = reg'SP)
                    (ß (aget this i'imm) = (inst >>> 0) & 0x7f)
                    (§ break)
                )

                #_"BLX <Rm>"
                #_"0 1 0 0 0 1 1 1 1 Rm (0) (0) (0)"
                (§ case code'BLX)
                (§
                    (ß (aget this i'rm) = (inst >>> 3) & 0xf)
                    (ß (aget this i'rd) = reg'LR)
                    (§ break)
                )

                #_"BX <Rm>"
                #_"0 1 0 0 0 1 1 1 0 Rm (0) (0) (0)"
                (§ case code'BX)
                (§
                    (ß (aget this i'rm) = (inst >>> 3) & 0xf)
                    (§ break)
                )

                (§ default)
                (§
                    (ß v_decoded = false)
                    (§ break)
                )
            )
        )

        ;; Group 5?
        (when (ß !v_decoded)
            (ß v_decoded = true)
            (ß (aget this i'inst_group) = code'IGRP5)
            (§ switch (inst & mask'IGRP5)
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
                    (ß (aget this i'rm) = (inst >>> 3) & 0x7)
                    (ß (aget this i'rd) = (inst >>> 0) & 0x7)
                    (ß (aget this i'rn) = (aget this i'rd))
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
                    (ß (aget this i'rm) = (inst >>> 3) & 0x7)
                    (ß (aget this i'rn) = (inst >>> 0) & 0x7)
                    (§ break)
                )

                #_"MULS <Rdm>,<Rn>,<Rdm>"
                #_"0 1 0 0 0 0 1 1 0 1 Rn Rdm"
                (§ case code'MULS)
                (§
                    (ß (aget this i'rn) = (inst >>> 3) & 0x7)
                    (ß (aget this i'rd) = (inst >>> 0) & 0x7)
                    (ß (aget this i'rm) = (aget this i'rd))
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
                    (ß (aget this i'rm) = (inst >>> 3) & 0x7)
                    (ß (aget this i'rd) = (inst >>> 0) & 0x7)
                    (§ break)
                )

                #_"RSBS <Rd>,<Rn>,#0"
                #_"0 1 0 0 0 0 1 0 0 1 Rn Rd"
                (§ case code'RSBS)
                (§
                    (ß (aget this i'rn) = (inst >>> 3) & 0x7)
                    (ß (aget this i'rd) = (inst >>> 0) & 0x7)
                    (§ break)
                )

                (§ default)
                (§
                    (ß v_decoded = false)
                    (§ break)
                )
            )
        )

        ;; Group 6?
        (when (ß !v_decoded)
            (ß v_decoded = true)
            (ß (aget this i'inst_group) = code'IGRP6)
            (§ switch (inst & mask'IGRP6)
                #_"MRS <Rd>,<spec_reg>"
                #_"1 1 1 01 0 1 1 1 1 1 (0) (1) (1) (1) (1) 1 0 (0) 0 Rd SYSm"
                (§ case code'MRS)
                (§
                    ;; 32-bit instruction
                    (ß res = true)
                    (§ break)
                )
                #_"MSR <spec_reg>,<Rn>"
                #_"1 1 1 01 0 1 1 1 0 0 (0) Rn 1 0 (0) 0 (1) (0) (0) (0) SYSm"
                (§ case code'MSR)
                (§
                    (ß (aget this i'rn) = (inst >>> 0) & 0xf)

                    ;; 32-bit instruction
                    (ß res = true)
                    (§ break)
                )
                #_"CPS<effect> i"
                #_"1 0 1 1 0 1 1 0 0 1 1 im (0) (0) (1) (0)"
                (§ case code'CPS)
                (§
                    (ß (aget this i'imm) = (inst >>> 4) & 0x1)
                    (§ break)
                )

                (§ default)
                (§
                    (ß v_decoded = false)
                    (§ break)
                )
            )
        )

        ;; Group 7?
        (when (ß !v_decoded)
            (ß v_decoded = true)
            (ß (aget this i'inst_group) = code'IGRP7)
            (§ switch (inst & mask'IGRP7)
                #_"DMB #<option>"
                #_"1 1 1 01 0 1 1 1 0 1 1 (1) (1) (1) (1) 1 0 (0) 0 (1) (1) (1) (1) 0 1 0 1 option"
             ;; case code'DMB:
                #_"DSB #<option>"
                #_"1 1 1 01 0 1 1 1 0 1 1 (1) (1) (1) (1) 1 0 (0) 0 (1) (1) (1) (1) 0 1 0 0 option"
             ;; case code'DSB:
                #_"ISB #<option>"
                #_"1 1 1 01 0 1 1 1 0 1 1 (1) (1) (1) (1) 1 0 (0) 0 (1) (1) (1) (1) 0 1 1 0 option"
                (§ case code'ISB)
                (§
                    ;; 32-bit instruction
                    (ß res = true)

                    ;; Do nothing
                    (§ break)
                )
                #_"UDF_W #<imm16>"
                #_"1 11 1 0 1 1 1 1 1 1 1 imm4 1 0 1 0 imm12"
                (§ case code'UDF_W)
                (§
                    ;; 32-bit instruction
                    (ß res = true)

                    ;; Do nothing
                    (§ break)
                )

                (§ default)
                (§
                    (ß v_decoded = false)
                    (§ break)
                )
            )
        )

        ;; Group 8?
        (when (ß !v_decoded)
            (ß v_decoded = true)
            (ß (aget this i'inst_group) = code'IGRP8)
            (§ switch (inst & mask'IGRP8)
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
                    (ß assert(0))
                    (§ break)
                )
                #_"YIELD"
                #_"1 0 1 1 1 1 1 1 0 0 0 1 0 0 0 0"
                (§ case code'YIELD)
                (§
                    ;; Do nothing
                    (ß assert(0))
                    (§ break)
                )

                (§ default)
                (§
                    (ß v_decoded = false)
                    (§ break)
                )
            )
        )

        (when (ß !v_decoded)
            (ß assert(!"Instruction decode failed"))
        )

        (§ return res)
    )

    (defn #_"void" armv6m_execute [#_"cpu" this, #_"u16" inst, #_"u16" inst2]
        (ß #_"u32" reg_rm = (aget this i'regfile)[(aget this i'rm)])
        (ß #_"u32" reg_rn = (aget this i'regfile)[(aget this i'rn)])
        (ß #_"u32" reg_rd = 0)
        (ß #_"u32" pc = (aget this i'regfile)[reg'PC])
        (ß #_"u32" offset = 0)
        (ß #_"bool" write_rd = false)

        (ß pc = pc + 2)

        (§ switch ((aget this i'inst_group))
            (§ case code'IGRP0)
            (§
                (§ switch (inst & mask'IGRP0)
                    #_"BCC <label>"
                    #_"1 1 0 1 cond imm8"
                    (§ case code'BCC)
                    (§
                        ;; Sign extend offset
                        (ß offset = armv6m_sign_extend(this, (aget this i'imm), 8))

                        ;; Convert to words
                        (ß offset = offset << 1)

                        ;; Make relative to PC + 4
                        (ß offset = offset + pc + 2)

                        (§ switch ((aget this i'cond))
                            (§ case 0) #_"EQ"
                            (§
                                (when (ß (aget this i'apsr) & APSR_Z)
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 1) #_"NE"
                            (§
                                (when (ß ((aget this i'apsr) & APSR_Z) == 0)
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 2) #_"CS/HS"
                            (§
                                (when (ß (aget this i'apsr) & APSR_C)
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 3) #_"CC/LO"
                            (§
                                (when (ß ((aget this i'apsr) & APSR_C) == 0)
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 4) #_"MI"
                            (§
                                (when (ß (aget this i'apsr) & APSR_N)
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 5) #_"PL"
                            (§
                                (when (ß ((aget this i'apsr) & APSR_N) == 0)
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 6) #_"VS"
                            (§
                                (when (ß (aget this i'apsr) & APSR_V)
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 7) #_"VC"
                            (§
                                (when (ß ((aget this i'apsr) & APSR_V) == 0)
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 8) #_"HI"
                            (§
                                (when (ß ((aget this i'apsr) & APSR_C) && (((aget this i'apsr) & APSR_Z) == 0))
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 9) #_"LS"
                            (§
                                (when (ß (((aget this i'apsr) & APSR_C) == 0) || ((aget this i'apsr) & APSR_Z))
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 10) #_"GE"
                            (§
                                (when (ß (((aget this i'apsr) & APSR_N) >>> shift'APSR_N) == (((aget this i'apsr) & APSR_V) >>> shift'APSR_V))
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 11) #_"LT"
                            (§
                                (when (ß (((aget this i'apsr) & APSR_N) >>> shift'APSR_N) != (((aget this i'apsr) & APSR_V) >>> shift'APSR_V))
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 12) #_"GT"
                            (§
                                (when (ß (((aget this i'apsr) & APSR_Z) == 0) && ((((aget this i'apsr) & APSR_N) >>> shift'APSR_N) == (((aget this i'apsr) & APSR_V) >>> shift'APSR_V)))
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 13) #_"LE"
                            (§
                                (when (ß ((aget this i'apsr) & APSR_Z) || ((((aget this i'apsr) & APSR_N) >>> shift'APSR_N) != (((aget this i'apsr) & APSR_V) >>> shift'APSR_V)))
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 14) #_"AL"
                            (§
                                (ß pc = offset)
                                (§ break)
                            )
                            (§ case 15) #_"SVC"
                            (§
                                (ß pc = armv6m_exception(this, pc, 11))
                                (§ break)
                            )
                            (§ default)
                            (§
                                (ß assert(!"Bad condition code"))
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
                (§ switch (inst & mask'IGRP1)
                    #_"ADDS <Rdn>,#<imm8>"
                    #_"0 0 1 1 0 Rdn imm8"
                    (§ case code'ADDS_1)
                    (§
                        (ß reg_rd = armv6m_add_with_carry(this, reg_rn, (aget this i'imm), 0, ALL_FLAGS))
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"ADD <Rd>,SP,#<imm8>"
                    #_"1 0 1 0 1 Rd imm8"
                    (§ case code'ADD_1)
                    (§
                        (ß reg_rd = reg_rn + ((aget this i'imm) << 2))
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"ADR <Rd>,<label>"
                    #_"1 0 1 0 0 Rd imm8"
                    (§ case code'ADR)
                    (§
                        (ß reg_rd = pc + (aget this i'imm) + 2)
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"ASRS <Rd>,<Rm>,#<imm5>"
                    #_"0 0 0 1 0 imm5 Rm Rd"
                    (§ case code'ASRS)
                    (§
                        (when (ß (aget this i'imm) == 0)
                            (ß (aget this i'imm) = 32)
                        )

                        (ß reg_rd = armv6m_arith_shift_right(this, reg_rm, (aget this i'imm), FLAGS_NZC))
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"B <label>"
                    #_"1 1 1 0 0 imm11"
                    (§ case code'B)
                    (§
                        ;; Sign extend offset
                        (ß offset = armv6m_sign_extend(this, (aget this i'imm), 11))

                        ;; Convert to words
                        (ß offset = offset << 1)

                        ;; Make relative to PC + 4
                        (ß offset = offset + pc + 2)

                        (ß pc = offset)
                        (§ break)
                    )
                    #_"BL <label>"
                    #_"1 1 1 01 S imm10 1 1 J1 1 J2 imm11"
                    (§ case code'BL)
                    (§
                        ;; Sign extend
                        (ß offset = armv6m_sign_extend(this, (aget this i'imm), 11))
                        (ß offset <<= 11)

                        ;; Additional range
                        (ß (aget this i'imm) = (inst2 >>> 0) & 0x7ff)
                        (ß offset |= (aget this i'imm))

                        ;; Make relative to PC
                        (ß offset <<= 1)
                        (ß offset = offset + pc)

                        ;; (aget this i'rd) = reg'LR
                        (ß reg_rd = (pc + 2) | 1)
                        (ß write_rd = true)

                        (ß pc = offset + 2)
                        (§ break)
                    )
                    #_"CMP <Rn>,#<imm8>"
                    #_"0 0 1 0 1 Rn imm8"
                    (§ case code'CMP)
                    (§
                        (ß reg_rd = armv6m_add_with_carry(this, reg_rn, (bit-not (aget this i'imm)), 1, ALL_FLAGS))
                        ;; No writeback
                        (§ break)
                    )
                    #_"LDM <Rn>!,<registers> <Rn> not included in <registers>"
                    #_"1 1 0 0 1 Rn register_list"
                    #_"LDM <Rn>,<registers> <Rn> included in <registers>"
                    #_"1 1 0 0 1 Rn register_list"
                 ;; case code'LDM_1:
                    (§ case code'LDM)
                    (§
                        (§ for (#_"s32" i = 0; i < REGISTERS && (aget this i'reglist) != 0; i++)
                            (when (ß (aget this i'reglist) & (1 << i))
                                (ß (aget this i'regfile)[i] = cpu''read32(this, reg_rn))
                                (when (ß i == reg'PC)
                                    (when (ß ((aget this i'regfile)[i] & EXC_RETURN) != EXC_RETURN)
                                        (ß (aget this i'regfile)[i] &= (bit-not 1))
                                    )
                                    (ß pc = (aget this i'regfile)[i])
                                )
                                (ß reg_rn = reg_rn + 4)
                                (ß (aget this i'reglist) &= (bit-not (1 << i)))
                            )
                        )

                        (ß (aget this i'regfile)[(aget this i'rd)] = reg_rn)
                        (ß assert((aget this i'rd) != reg'PC))
                        (§ break)
                    )
                    #_"LDR <Rt>, [<Rn>{,#<imm5>}]"
                    #_"0 1 1 0 1 imm5 Rn Rt"
                    (§ case code'LDR)
                    (§
                        (ß (aget this i'regfile)[(aget this i'rt)] = cpu''read32(this, reg_rn + ((aget this i'imm) << 2)))
                        (ß assert((aget this i'rd) != reg'PC))
                        (§ break)
                    )
                    #_"LDR <Rt>,[SP{,#<imm8>}]"
                    #_"1 0 0 1 1 Rt imm8"
                    (§ case code'LDR_1)
                    (§
                        (ß (aget this i'regfile)[(aget this i'rt)] = cpu''read32(this, reg_rn + ((aget this i'imm) << 2)))
                        (ß assert((aget this i'rd) != reg'PC))
                        (§ break)
                    )
                    #_"LDR <Rt>,<label>"
                    #_"0 1 0 0 1 Rt imm8"
                    (§ case code'LDR_2)
                    (§
                        (ß (aget this i'regfile)[(aget this i'rt)] = cpu''read32(this, ((aget this i'regfile)[reg'PC] & 0xfffffffc) + ((aget this i'imm) << 2) + 4))
                        (ß assert((aget this i'rd) != reg'PC))
                        (§ break)
                    )
                    #_"LDRB <Rt>,[<Rn>{,#<imm5>}]"
                    #_"0 1 1 1 1 imm5 Rn Rt"
                    (§ case code'LDRB)
                    (§
                        (ß (aget this i'regfile)[(aget this i'rt)] = cpu''read8(this, reg_rn + (aget this i'imm)))
                        (§ break)
                    )
                    #_"LDRH <Rt>,[<Rn>{,#<imm5>}]"
                    #_"1 0 0 0 1 imm5 Rn Rt"
                    (§ case code'LDRH)
                    (§
                        (ß (aget this i'regfile)[(aget this i'rt)] = cpu''read16(this, reg_rn + ((aget this i'imm) << 1)))
                        (§ break)
                    )
                    #_"LSLS <Rd>,<Rm>,#<imm5>"
                    #_"0 0 0 0 0 imm5 Rm Rd"
                    #_"MOVS <Rd>,<Rm>"
                    #_"0 0 0 0 0 0 0 0 0 0 Rm Rd"
                 ;; case code'MOVS_1:
                    (§ case code'LSLS)
                    (§
                        (if (ß (aget this i'imm) == 0)
                            (do
                                ;; MOVS <Rd>,<Rm>
                                (ß reg_rd = reg_rm)
                                (ß write_rd = true)

                                ;; Update N & Z
                                (ß armv6m_update_n_z_flags(this, reg_rd))
                            )
                            (do
                                ;; LSLS <Rd>,<Rm>,#<imm5>
                                (ß reg_rd = armv6m_shift_left(this, reg_rm, (aget this i'imm), FLAGS_NZC))
                                (ß write_rd = true)
                            )
                        )
                        (§ break)
                    )
                    #_"LSRS <Rd>,<Rm>,#<imm5>"
                    #_"0 0 0 0 1 imm5 Rm Rd"
                    (§ case code'LSRS)
                    (§
                        (when (ß (aget this i'imm) == 0)
                            (ß (aget this i'imm) = 32)
                        )

                        (ß reg_rd = armv6m_shift_right(this, reg_rm, (aget this i'imm), FLAGS_NZC))
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"MOVS <Rd>,#<imm8>"
                    #_"0 0 1 0 0 Rd imm8"
                    (§ case code'MOVS)
                    (§
                        (ß reg_rd = (aget this i'imm))
                        (ß write_rd = true)

                        (ß armv6m_update_n_z_flags(this, reg_rd))
                        (§ break)
                    )
                    #_"STM <Rn>!,<registers>"
                    #_"1 1 0 0 0 Rn register_list"
                    (§ case code'STM)
                    (§
                        (ß #_"u32" addr = reg_rn)

                        (§ for (#_"s32" i = 0; i < REGISTERS && (aget this i'reglist) != 0; i++)
                            (when (ß (aget this i'reglist) & (1 << i))
                                (ß cpu''write32(this, addr, (aget this i'regfile)[i]))
                                (ß addr = addr + 4)
                                (ß (aget this i'reglist) &= (bit-not (1 << i)))
                            )
                        )

                        (ß reg_rd = addr)
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"STR <Rt>, [<Rn>{,#<imm5>}]"
                    #_"0 1 1 0 0 imm5 Rn Rt"
                    (§ case code'STR)
                    (§
                        (ß cpu''write32(this, reg_rn + ((aget this i'imm) << 2), (aget this i'regfile)[(aget this i'rt)]))
                        (§ break)
                    )
                    #_"STR <Rt>,[SP,#<imm8>]"
                    #_"1 0 0 1 0 Rt imm8"
                    (§ case code'STR_1)
                    (§
                        (ß cpu''write32(this, reg_rn + ((aget this i'imm) << 2), (aget this i'regfile)[(aget this i'rt)]))
                        (§ break)
                    )
                    #_"STRB <Rt>,[<Rn>,#<imm5>]"
                    #_"0 1 1 1 0 imm5 Rn Rt"
                    (§ case code'STRB)
                    (§
                        (ß cpu''write8(this, reg_rn + (aget this i'imm), (aget this i'regfile)[(aget this i'rt)]))
                        (§ break)
                    )
                    #_"STRH <Rt>,[<Rn>{,#<imm5>}]"
                    #_"1 0 0 0 0 imm5 Rn Rt"
                    (§ case code'STRH)
                    (§
                        (ß cpu''write16(this, reg_rn + ((aget this i'imm) << 1), (aget this i'regfile)[(aget this i'rt)]))
                        (§ break)
                    )
                    #_"SUBS <Rdn>,#<imm8>"
                    #_"0 0 1 11 Rdn imm8"
                    (§ case code'SUBS_1)
                    (§
                        (ß reg_rd = armv6m_add_with_carry(this, reg_rn, (bit-not (aget this i'imm)), 1, ALL_FLAGS))
                        (ß write_rd = true)
                        (§ break)
                    )
                )
                (§ break)
            )
            (§ case code'IGRP2)
            (§
                (§ switch (inst & mask'IGRP2)
                    #_"ADDS <Rd>,<Rn>,#<imm3>"
                    #_"0 0 0 1 1 1 0 imm3 Rn Rd"
                    (§ case code'ADDS)
                    (§
                        (ß reg_rd = armv6m_add_with_carry(this, reg_rn, (aget this i'imm), 0, ALL_FLAGS))
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"ADDS <Rd>,<Rn>,<Rm>"
                    #_"0 0 0 1 1 0 0 Rm Rn Rd"
                    (§ case code'ADDS_2)
                    (§
                        (ß reg_rd = armv6m_add_with_carry(this, reg_rn, reg_rm, 0, ALL_FLAGS))
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"LDR <Rt>,[<Rn>,<Rm>]"
                    #_"0 1 0 1 1 0 0 Rm Rn Rt"
                    (§ case code'LDR_3)
                    (§
                        (ß (aget this i'regfile)[(aget this i'rt)] = cpu''read32(this, reg_rn + reg_rm))
                        (ß assert((aget this i'rt) != reg'PC))
                        (§ break)
                    )
                    #_"LDRB <Rt>,[<Rn>,<Rm>]"
                    #_"0 1 0 1 1 1 0 Rm Rn Rt"
                    (§ case code'LDRB_1)
                    (§
                        (ß (aget this i'regfile)[(aget this i'rt)] = cpu''read8(this, reg_rn + reg_rm))
                        (§ break)
                    )
                    #_"LDRH <Rt>,[<Rn>,<Rm>]"
                    #_"0 1 0 1 1 0 1 Rm Rn Rt"
                    (§ case code'LDRH_1)
                    (§
                        (ß (aget this i'regfile)[(aget this i'rt)] = cpu''read16(this, reg_rn + reg_rm))
                        (§ break)
                    )
                    #_"LDRSB <Rt>,[<Rn>,<Rm>]"
                    #_"0 1 0 1 0 1 1 Rm Rn Rt"
                    (§ case code'LDRSB)
                    (§
                        (ß reg_rd = cpu''read8(this, reg_rn + reg_rm))
                        (ß (aget this i'regfile)[(aget this i'rt)] = armv6m_sign_extend(this, reg_rd, 8))
                        (§ break)
                    )
                    #_"LDRSH <Rt>,[<Rn>,<Rm>]"
                    #_"0 1 0 1 1 1 1 Rm Rn Rt"
                    (§ case code'LDRSH)
                    (§
                        (ß reg_rd = cpu''read16(this, reg_rn + reg_rm))
                        (ß (aget this i'regfile)[(aget this i'rt)] = armv6m_sign_extend(this, reg_rd, 16))
                        (§ break)
                    )
                    #_"POP <registers>"
                    #_"1 0 1 1 1 1 0 P register_list"
                    (§ case code'POP)
                    (§
                        (ß #_"u32" sp = (aget this i'regfile)[reg'SP])

                        (§ for (#_"s32" i = 0; i < REGISTERS && (aget this i'reglist) != 0; i++)
                            (when (ß (aget this i'reglist) & (1 << i))
                                (ß (aget this i'regfile)[i] = cpu''read32(this, sp))

                                (ß sp = sp + 4)

                                (when (ß i == reg'PC)
                                    (when (ß ((aget this i'regfile)[i] & EXC_RETURN) != EXC_RETURN)
                                        (ß (aget this i'regfile)[i] &= (bit-not 1))
                                    )
                                    (ß pc = (aget this i'regfile)[i])
                                )

                                (ß (aget this i'reglist) &= (bit-not (1 << i)))
                            )
                        )

                        (ß armv6m_update_sp(this, sp))
                        (§ break)
                    )
                    #_"PUSH <registers>"
                    #_"1 0 1 1 0 1 0 M register_list"
                    (§ case code'PUSH)
                    (§
                        (ß #_"u32" sp = (aget this i'regfile)[reg'SP])
                        (ß #_"u32" addr = sp)
                        (ß #_"s32" bits_set = 0)

                        (§ for (#_"s32" i = 0; i < REGISTERS; i++)
                            (when (ß (aget this i'reglist) & (1 << i))
                                (ß bits_set++)
                            )
                        )

                        (ß addr = addr - (4 * bits_set))

                        (§ for (#_"s32" i = 0; i < REGISTERS && (aget this i'reglist) != 0; i++)
                            (when (ß (aget this i'reglist) & (1 << i))
                                (ß cpu''write32(this, addr, (aget this i'regfile)[i]))
                                (ß sp = sp - 4)
                                (ß addr = addr + 4)
                                (ß (aget this i'reglist) &= (bit-not (1 << i)))
                            )
                        )

                        (ß armv6m_update_sp(this, sp))
                        (§ break)
                    )
                    #_"STR <Rt>,[<Rn>,<Rm>]"
                    #_"0 1 0 1 0 00 Rm Rn Rt"
                    (§ case code'STR_2)
                    (§
                        (ß cpu''write32(this, reg_rn + reg_rm, (aget this i'regfile)[(aget this i'rt)]))
                        (§ break)
                    )
                    #_"STRB <Rt>,[<Rn>,<Rm>]"
                    #_"0 1 0 1 0 1 0 Rm Rn Rt"
                    (§ case code'STRB_1)
                    (§
                        (ß cpu''write8(this, reg_rn + reg_rm, (aget this i'regfile)[(aget this i'rt)]))
                        (§ break)
                    )
                    #_"STRH <Rt>,[<Rn>,<Rm>]"
                    #_"0 1 0 1 0 0 1 Rm Rn Rt"
                    (§ case code'STRH_1)
                    (§
                        (ß cpu''write16(this, reg_rn + reg_rm, (aget this i'regfile)[(aget this i'rt)]))
                        (§ break)
                    )
                    #_"SUBS <Rd>,<Rn>,#<imm3>"
                    #_"0 0 0 11 1 1 imm3 Rn Rd"
                    (§ case code'SUBS)
                    (§
                        (ß reg_rd = armv6m_add_with_carry(this, reg_rn, (bit-not (aget this i'imm)), 1, ALL_FLAGS))
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"SUBS <Rd>,<Rn>,<Rm>"
                    #_"0 0 0 11 0 1 Rm Rn Rd"
                    (§ case code'SUBS_2)
                    (§
                        (ß reg_rd = armv6m_add_with_carry(this, reg_rn, (bit-not reg_rm), 1, ALL_FLAGS))
                        (ß write_rd = true)
                        (§ break)
                    )
                )
                (§ break)
            )
            (§ case code'IGRP3)
            (§
                (§ switch (inst & mask'IGRP3)
                    #_"ADD <Rdn>,<Rm>"
                    #_"0 1 0 0 0 1 0 0 Rm Rdn"
                    (§ case code'ADD)
                    (§
                        (ß reg_rd = reg_rn + reg_rm)
                        (ß write_rd = true)
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
                        (ß reg_rd = armv6m_add_with_carry(this, reg_rn, (bit-not reg_rm), 1, ALL_FLAGS))
                        (§ break)
                    )
                    #_"MOV <Rd>,<Rm> Otherwise all versions of the Thumb instruction set."
                    #_"0 1 0 0 0 1 1 0 D Rm Rd"
                    (§ case code'MOV)
                    (§
                        (if (ß (aget this i'rd) == reg'PC)
                            (do
                                ;; Write to PC
                                (ß pc = reg_rm & (bit-not 1))

                                ;; Don't do normal writeback
                                (ß write_rd = false)
                            )
                            (do
                                ;; Normal register
                                (ß reg_rd = reg_rm)
                                (ß write_rd = true)
                            )
                        )
                        (§ break)
                    )
                    #_"SVC #<imm8>"
                    #_"1 1 0 1 111 1 imm8"
                    (§ case code'SVC)
                    (§
                        (ß pc = armv6m_exception(this, pc, 11))
                        (§ break)
                    )
                    #_"UDF #<imm8>"
                    #_"1 1 0 1 1 1 1 0 imm8"
                    (§ case code'UDF)
                    (§
                        (ß assert(!"Not implemented"))
                        (§ break)
                    )
                )
                (§ break)
            )
            (§ case code'IGRP4)
            (§
                (§ switch (inst & mask'IGRP4)
                    #_"ADD SP,SP,#<imm7>"
                    #_"1 0 1 1 0 0 0 0 0 imm7"
                    (§ case code'ADD_2)
                    (§
                        (ß reg_rd = reg_rn + ((aget this i'imm) << 2))
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"BLX <Rm>"
                    #_"0 1 0 0 0 1 1 1 1 Rm (0) (0) (0)"
                    (§ case code'BLX)
                    (§
                        ;; (aget this i'rd) = reg'LR
                        (ß reg_rd = pc | 1)
                        (ß write_rd = true)

                        (ß pc = reg_rm & (bit-not 1))
                        (§ break)
                    )
                    #_"BX <Rm>"
                    #_"0 1 0 0 0 1 1 1 0 Rm (0) (0) (0)"
                    (§ case code'BX)
                    (§
                        (ß pc = reg_rm & (bit-not 1))
                        (§ break)
                    )
                    #_"SUB SP,SP,#<imm7>"
                    #_"1 0 1 1 000 0 1 imm7"
                    (§ case code'SUB)
                    (§
                        (ß reg_rd = reg_rn - ((aget this i'imm) << 2))
                        (ß write_rd = true)
                        (§ break)
                    )
                )
                (§ break)
            )
            (§ case code'IGRP5)
            (§
                (§ switch (inst & mask'IGRP5)
                    #_"ADCS <Rdn>,<Rm>"
                    #_"0 1 0 0 0 0 0 1 0 1 Rm Rdn"
                    (§ case code'ADCS)
                    (§
                        (ß reg_rd = armv6m_add_with_carry(this, reg_rn, reg_rm, ((aget this i'apsr) & APSR_C) ? 1 : 0, ALL_FLAGS))
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"ANDS <Rdn>,<Rm>"
                    #_"0 1 0 0 0 0 0 0 0 0 Rm Rdn"
                    (§ case code'ANDS)
                    (§
                        (ß reg_rd = reg_rn & reg_rm)
                        (ß write_rd = true)

                        (ß armv6m_update_n_z_flags(this, reg_rd))
                        (§ break)
                    )
                    #_"ASRS <Rdn>,<Rm>"
                    #_"0 1 0 0 0 0 0 1 0 0 Rm Rdn"
                    (§ case code'ASRS_1)
                    (§
                        (ß reg_rd = armv6m_arith_shift_right(this, reg_rn, reg_rm, FLAGS_NZC))
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"BICS <Rdn>,<Rm>"
                    #_"0 1 0 0 0 0 1 1 1 0 Rm Rdn"
                    (§ case code'BICS)
                    (§
                        (ß reg_rd = reg_rn & (bit-not reg_rm))
                        (ß write_rd = true)

                        (ß armv6m_update_n_z_flags(this, reg_rd))
                        (§ break)
                    )
                    #_"CMN <Rn>,<Rm>"
                    #_"0 1 0 0 0 0 1 0 1 1 Rm Rn"
                    (§ case code'CMN)
                    (§
                        (ß reg_rd = armv6m_add_with_carry(this, reg_rn, reg_rm, 0, ALL_FLAGS))
                        (§ break)
                    )
                    #_"CMP <Rn>,<Rm> <Rn> and <Rm> both from R0-R7"
                    #_"0 1 0 0 0 0 1 0 1 0 Rm Rn"
                    (§ case code'CMP_1)
                    (§
                        (ß reg_rd = armv6m_add_with_carry(this, reg_rn, (bit-not reg_rm), 1, ALL_FLAGS))
                        (§ break)
                    )
                    #_"EORS <Rdn>,<Rm>"
                    #_"0 1 0 0 0 0 0 0 0 1 Rm Rdn"
                    (§ case code'EORS)
                    (§
                        (ß reg_rd = reg_rn ^ reg_rm)
                        (ß write_rd = true)

                        (ß armv6m_update_n_z_flags(this, reg_rd))
                        (§ break)
                    )
                    #_"LSLS <Rdn>,<Rm>"
                    #_"0 1 0 0 0 0 0 0 1 0 Rm Rdn"
                    (§ case code'LSLS_1)
                    (§
                        (if (ß reg_rm == 0)
                            (do
                                (ß reg_rd = reg_rn)
                                (ß write_rd = true)

                                ;; Update N & Z
                                (ß armv6m_update_n_z_flags(this, reg_rd))
                            )
                            (do
                                (ß reg_rd = armv6m_shift_left(this, reg_rn, reg_rm, FLAGS_NZC))
                                (ß write_rd = true)
                            )
                        )
                        (§ break)
                    )
                    #_"LSRS <Rdn>,<Rm>"
                    #_"0 1 0 0 0 0 0 0 1 1 Rm Rdn"
                    (§ case code'LSRS_1)
                    (§
                        (ß reg_rd = armv6m_shift_right(this, reg_rn, reg_rm & 0xff, FLAGS_NZC))
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"MULS <Rdm>,<Rn>,<Rdm>"
                    #_"0 1 0 0 0 0 1 1 0 1 Rn Rdm"
                    (§ case code'MULS)
                    (§
                        (ß reg_rd = reg_rn * reg_rm)
                        (ß write_rd = true)

                        (ß armv6m_update_n_z_flags(this, reg_rd))
                        (§ break)
                    )
                    #_"MVNS <Rd>,<Rm>"
                    #_"0 1 0 0 0 0 1 1 1 1 Rm Rd"
                    (§ case code'MVNS)
                    (§
                        (ß reg_rd = (bit-not reg_rm))
                        (ß write_rd = true)

                        (ß armv6m_update_n_z_flags(this, reg_rd))
                        (§ break)
                    )
                    #_"ORRS <Rdn>,<Rm>"
                    #_"0 1 0 0 0 0 1 1 0 0 Rm Rdn"
                    (§ case code'ORRS)
                    (§
                        (ß reg_rd = reg_rn | reg_rm)
                        (ß write_rd = true)

                        (ß armv6m_update_n_z_flags(this, reg_rd))
                        (§ break)
                    )
                    #_"REV <Rd>,<Rm>"
                    #_"1 0 1 1 1 0 1 0 0 0 Rm Rd"
                    (§ case code'REV)
                    (§
                        (ß reg_rd = ((reg_rm >>> 0) & 0xff) << 24)
                        (ß reg_rd |= ((reg_rm >>> 8) & 0xff) << 16)
                        (ß reg_rd |= ((reg_rm >>> 16) & 0xff) << 8)
                        (ß reg_rd |= ((reg_rm >>> 24) & 0xff) << 0)
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"REV16 <Rd>,<Rm>"
                    #_"1 0 1 1 1 0 1 0 0 1 Rm Rd"
                    (§ case code'REV16)
                    (§
                        (ß reg_rd = ((reg_rm >>> 0) & 0xff) << 8)
                        (ß reg_rd |= ((reg_rm >>> 8) & 0xff) << 0)
                        (ß reg_rd |= ((reg_rm >>> 16) & 0xff) << 24)
                        (ß reg_rd |= ((reg_rm >>> 24) & 0xff) << 16)
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"REVSH <Rd>,<Rm>"
                    #_"1 0 1 1 1 0 1 0 1 1 Rm Rd"
                    (§ case code'REVSH)
                    (§
                        (ß reg_rd = ((reg_rm >>> 0) & 0xff) << 8)
                        (ß reg_rd |= ((reg_rm >>> 8) & 0xff) << 0)
                        (ß reg_rd = armv6m_sign_extend(this, reg_rd, 16))
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"RORS <Rdn>,<Rm>"
                    #_"0 1 0 0 0 0 0 1 1 1 Rm Rdn"
                    (§ case code'RORS)
                    (§
                        (ß reg_rd = armv6m_rotate_right(this, reg_rn, reg_rm & 0xff, FLAGS_NZC))
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"RSBS <Rd>,<Rn>,#0"
                    #_"0 1 0 0 0 0 1 0 0 1 Rn Rd"
                    (§ case code'RSBS)
                    (§
                        (ß reg_rd = armv6m_add_with_carry(this, (bit-not reg_rn), 0, 1, ALL_FLAGS))
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"SBCS <Rdn>,<Rm>"
                    #_"0 1 0 0 0 0 0 1 1 0 Rm Rdn"
                    (§ case code'SBCS)
                    (§
                        (ß reg_rd = armv6m_add_with_carry(this, reg_rn, (bit-not reg_rm), ((aget this i'apsr) & APSR_C) ? 1 : 0, ALL_FLAGS))
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"SXTB <Rd>,<Rm>"
                    #_"1 0 1 1 100 0 0 1 Rm Rd"
                    (§ case code'SXTB)
                    (§
                        (ß reg_rd = reg_rm & 0xff)
                        (when (ß reg_rd & 0x80)
                            (ß reg_rd |= (bit-not 0) << 8)
                        )
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"SXTH <Rd>,<Rm>"
                    #_"1 0 1 1 100 0 0 0 Rm Rd"
                    (§ case code'SXTH)
                    (§
                        (ß reg_rd = reg_rm & 0xffff)
                        (when (ß reg_rd & 0x8000)
                            (ß reg_rd |= (bit-not 0) << 16)
                        )
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"TST <Rn>,<Rm>"
                    #_"000 1 0 0 1 0 0 0 Rm Rn"
                    (§ case code'TST)
                    (§
                        (ß reg_rd = reg_rn & reg_rm)
                        ;; No writeback
                        (ß armv6m_update_n_z_flags(this, reg_rd))
                        (§ break)
                    )
                    #_"UXTB <Rd>,<Rm>"
                    #_"1 0 1 1 100 0 1 1 Rm Rd"
                    (§ case code'UXTB)
                    (§
                        (ß reg_rd = reg_rm & 0xff)
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"UXTH <Rd>,<Rm>"
                    #_"1 0 1 1 100 0 1 0 Rm Rd"
                    (§ case code'UXTH)
                    (§
                        (ß reg_rd = reg_rm & 0xffff)
                        (ß write_rd = true)
                        (§ break)
                    )
                )
                (§ break)
            )
            (§ case code'IGRP6)
            (§
                (§ switch (inst & mask'IGRP6)
                    #_"MRS <Rd>,<spec_reg>"
                    #_"1 1 1 01 0 1 1 1 1 1 (0) (1) (1) (1) (1) 1 0 (0) 0 Rd SYSm"
                    (§ case code'MRS)
                    (§
                        (ß #_"u32" sysm = (inst2 >>> 0) & 0xff)
                        (ß (aget this i'rd) = (inst2 >>> 8) & 0xf)

                        ;; Increment PC past second instruction word
                        (ß pc = pc + 2)

                        (§ switch ((sysm >>> 3) & 0x1f)
                            (§ case 0)
                            (§
                                (ß #_"u32" val = 0)

                                (when (ß sysm & 0x1)
                                    (ß val |= (aget this i'ipsr) & 0x1ff)
                                )

                                (when (ß !(sysm & 0x4))
                                    (ß val |= ((aget this i'apsr) & 0xf8000000))
                                )

                                (ß val |= (aget this i'ipsr))
                                (ß val |= (aget this i'epsr))

                                (ß reg_rd = val)
                                (ß write_rd = true)
                                (§ break)
                            )
                            (§ case 1)
                            (§
                                (§ switch (sysm & 0x7)
                                    (§ case 0)
                                    (§
                                        ;; Main SP
                                        (ß reg_rd = (aget this i'msp))
                                        (ß write_rd = true)
                                        (§ break)
                                    )
                                    (§ case 1)
                                    (§
                                        ;; Process SP
                                        (ß reg_rd = (aget this i'psp))
                                        (ß write_rd = true)
                                        (§ break)
                                    )
                                )
                                (§ break)
                            )
                            (§ case 2)
                            (§
                                (§ switch (sysm & 0x7)
                                    (§ case 0)
                                    (§
                                        ;; PRIMASK.PM
                                        (ß reg_rd = (aget this i'primask) & PRIMASK_PM)
                                        (ß write_rd = true)
                                        (§ break)
                                    )
                                    (§ case 4)
                                    (§
                                        ;; Control<1:0>
                                        (ß reg_rd = (aget this i'control) & CONTROL_MASK)
                                        (ß write_rd = true)
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
                        (ß #_"u32" sysm = (inst2 >>> 0) & 0xff)

                        ;; Increment PC past second instruction word
                        (ß pc = pc + 2)

                        (§ switch ((sysm >>> 3) & 0x1f)
                            (§ case 0)
                            (§
                                (when (ß !(sysm & 0x4))
                                    (ß (aget this i'apsr) = reg_rn & 0xf8000000)
                                )
                                (§ break)
                            )
                            (§ case 1)
                            (§
                                ;; TODO: Only if privileged...
                                (§ switch (sysm & 0x7)
                                    (§ case 0)
                                    (§
                                        ;; Main SP
                                        (ß (aget this i'msp) = reg_rn)
                                        (§ break)
                                    )
                                    (§ case 1)
                                    (§
                                        ;; Process SP
                                        (ß (aget this i'psp) = reg_rn)
                                        (§ break)
                                    )
                                )
                                (§ break)
                            )
                            (§ case 2)
                            (§
                                ;; TODO: Only if privileged...
                                (§ switch (sysm & 0x7)
                                    (§ case 0)
                                    (§
                                        ;; PRIMASK.PM
                                        (ß (aget this i'primask) = reg_rn & PRIMASK_PM)
                                        (§ break)
                                    )
                                    (§ case 4)
                                    (§
                                        ;; Control<1:0>
                                        (when (ß !(aget this i'handler?))
                                            (ß (aget this i'control) = reg_rn & CONTROL_MASK)

                                            ;; Allow switching of current SP
                                         ;; (if (ß (aget this i'control) & CONTROL_SPSEL)
                                         ;;     spsel = SP_MSP;
                                         ;;     spsel = SP_PSP;
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

                        (if (ß (aget this i'imm) == 0)
                            (do
                                ;; Enable
                                (ß (aget this i'primask) &= (bit-not PRIMASK_PM))
                            )
                            (do
                                ;; Disable
                                (ß (aget this i'primask) |= PRIMASK_PM)
                            )
                        )
                        (§ break)
                    )
                )
                (§ break)
            )
            (§ case code'IGRP7)
            (§
                (§ switch (inst & mask'IGRP7)
                    #_"DMB #<option>"
                    #_"1 1 1 01 0 1 1 1 0 1 1 (1) (1) (1) (1) 1 0 (0) 0 (1) (1) (1) (1) 0 1 0 1 option"
                 ;; case code'DMB:
                    #_"DSB #<option>"
                    #_"1 1 1 01 0 1 1 1 0 1 1 (1) (1) (1) (1) 1 0 (0) 0 (1) (1) (1) (1) 0 1 0 0 option"
                 ;; case code'DSB:
                    #_"ISB #<option>"
                    #_"1 1 1 01 0 1 1 1 0 1 1 (1) (1) (1) (1) 1 0 (0) 0 (1) (1) (1) (1) 0 1 1 0 option"
                    (§ case code'ISB)
                    (§
                        ;; Increment PC past second instruction word
                        (ß pc = pc + 2)
                        (§ break)
                    )
                    #_"UDF_W #<imm16>"
                    #_"1 11 1 0 1 1 1 1 1 1 1 imm4 1 0 1 0 imm12"
                    (§ case code'UDF_W)
                    (§
                        ;; Increment PC past second instruction word
                        (ß pc = pc + 2)
                        (§ break)
                    )
                )
                (§ break)
            )
            (§ case code'IGRP8)
            (§
                (§ switch (inst & mask'IGRP8)
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
                        (ß assert(!"Not implemented"))
                        (§ break)
                    )
                    #_"YIELD"
                    #_"1 0 1 1 1 1 1 1 0 0 0 1 0 0 0 0"
                    (§ case code'YIELD)
                    (§
                        (ß assert(!"Not implemented"))
                        (§ break)
                    )
                )
                (§ break)
            )
        )

        (when (ß write_rd)
            (if (ß (aget this i'rd) == reg'SP)
                (ß armv6m_update_sp(this, reg_rd))
                (ß (aget this i'regfile)[(aget this i'rd)] = reg_rd)
            )
        )

        ;; Can't perform a writeback to PC using normal mechanism as this is a special register...
        (when (ß write_rd)
            (ß assert((aget this i'rd) != reg'PC))
        )

        (ß (aget this i'regfile)[reg'PC] = pc)
        nil
    )
)
