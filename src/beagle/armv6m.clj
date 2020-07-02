(ns beagle.armv6m
    (:refer-clojure :only [cons defmacro defn when])
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

    (defn #_"ram" ram'new [#_"u32" base, #_"u32" size]
        (ß #_"u32" (:m_base this) = base)
        (ß #_"u32" (:m_size this) = size)
        (ß #_"[u8]" (:m_mem this) = new #_"u8"[size])
        this
    )

    (defn #_"bool" ram''valid? [#_"ram" this, #_"u32" addr]
        (§ return ((:m_base this) <= addr) && (addr < ((:m_base this) + (:m_size this))))
    )

    (defn #_"void" ram''write8 [#_"ram" this, #_"u32" addr, #_"u8" data]
        (ß (:m_mem this)[addr - (:m_base this)] = data)
        nil
    )

    (defn #_"void" ram''write16 [#_"ram" this, #_"u32" addr, #_"u32" data]
        (ß ram''write8(this, addr + 0, data >> 0))
        (ß ram''write8(this, addr + 1, data >> 8))
        nil
    )

    (defn #_"void" ram''write32 [#_"ram" this, #_"u32" addr, #_"u32" data]
        (ß ram''write8(this, addr + 0, data >> 0))
        (ß ram''write8(this, addr + 1, data >> 8))
        (ß ram''write8(this, addr + 2, data >> 16))
        (ß ram''write8(this, addr + 3, data >> 24))
        nil
    )

    (defn #_"u8" ram''read8 [#_"ram" this, #_"u32" addr]
        (§ return (:m_mem this)[addr - (:m_base this)])
    )

    (defn #_"u16" ram''read16 [#_"ram" this, #_"u32" addr]
        (ß #_"u16" data = 0)

        (ß data |= ((#_"u32")ram''read8(this, addr + 0)) << 0)
        (ß data |= ((#_"u32")ram''read8(this, addr + 1)) << 8)

        (§ return data)
    )

    (defn #_"u32" ram''read32 [#_"ram" this, #_"u32" addr]
        (ß #_"u32" data = 0)

        (ß data |= ((#_"u32")ram''read8(this, addr + 0)) << 0)
        (ß data |= ((#_"u32")ram''read8(this, addr + 1)) << 8)
        (ß data |= ((#_"u32")ram''read8(this, addr + 2)) << 16)
        (ß data |= ((#_"u32")ram''read8(this, addr + 3)) << 24)

        (§ return data)
    )
)

(about #_"cpu"

    (defn #_"void" cpu''write8 [#_"cpu" this, #_"u32" addr, #_"u8" data]
        (§ for (#_"ram" mem = (:m_ram this); mem != nil; mem = (:next mem))
            (when (ß ram''valid?(mem, addr))
                (ß ram''write8(mem, addr, data))
                (§ return nil)
            )
        )
        nil
    )

    (defn #_"void" cpu''write16 [#_"cpu" this, #_"u32" addr, #_"u16" data]
        (ß addr &= ~1)

        (§ for (#_"ram" mem = (:m_ram this); mem != nil; mem = (:next mem))
            (when (ß ram''valid?(mem, addr))
                (ß ram''write16(mem, addr, data))
                (§ return nil)
            )
        )
        nil
    )

    (defn #_"void" cpu''write32 [#_"cpu" this, #_"u32" addr, #_"u32" data]
        (ß addr &= ~3)

        (§ for (#_"ram" mem = (:m_ram this); mem != nil; mem = (:next mem))
            (when (ß ram''valid?(mem, addr))
                (ß ram''write32(mem, addr, data))
                (§ return nil)
            )
        )
        nil
    )

    (defn #_"u8" cpu''read8 [#_"cpu" this, #_"u32" addr]
        (§ for (#_"ram" mem = (:m_ram this); mem != nil; mem = (:next mem))
            (when (ß ram''valid?(mem, addr))
                (§ return ram''read8(mem, addr))
            )
        )

        (§ return 0)
    )

    (defn #_"u16" cpu''read16 [#_"cpu" this, #_"u32" addr]
        (ß addr &= ~1)

        (§ for (#_"ram" mem = (:m_ram this); mem != nil; mem = (:next mem))
            (when (ß ram''valid?(mem, addr))
                (§ return ram''read16(mem, addr))
            )
        )

        (§ return 0)
    )

    (defn #_"u32" cpu''read32 [#_"cpu" this, #_"u32" addr]
        (ß addr &= ~3)

        (§ for (#_"ram" mem = (:m_ram this); mem != nil; mem = (:next mem))
            (when (ß ram''valid?(mem, addr))
                (§ return ram''read32(mem, addr))
            )
        )

        (§ return 0)
    )

    (def reg'SP    13)
    (def reg'LR    14)
    (def reg'PC    15)
    (def REGISTERS 16)

    (def APSR_N_SHIFT 31)
    (def APSR_Z_SHIFT 30)
    (def APSR_C_SHIFT 29)
    (def APSR_V_SHIFT 28)

    (def APSR_N (ß 1 << APSR_N_SHIFT))
    (def APSR_Z (ß 1 << APSR_Z_SHIFT))
    (def APSR_C (ß 1 << APSR_C_SHIFT))
    (def APSR_V (ß 1 << APSR_V_SHIFT))

    (def ALL_FLAGS (ß APSR_N | APSR_Z | APSR_C | APSR_V))
    (def FLAGS_NZC (ß APSR_N | APSR_Z | APSR_C))

    (def PRIMASK_PM (ß 1 << 0))

    (def CONTROL_NPRIV (ß 1 << 0))
    (def CONTROL_SPSEL (ß 1 << 1))
    (def CONTROL_MASK  (ß CONTROL_NPRIV | CONTROL_SPSEL))

    (def EXC_RETURN 0xffffffe0)

    (defn #_"cpu" cpu'new [#_"u32" base, #_"u32" size]
        (ß #_"ram*" :m_ram)

        (ß #_"u32" :m_regfile[16])
        (ß #_"u32" :m_psp)
        (ß #_"u32" :m_msp)
        (ß #_"u32" :m_apsr)
        (ß #_"u32" :m_ipsr)
        (ß #_"u32" :m_epsr)

        (ß #_"u32" :m_primask)
        (ß #_"u32" :m_control)

        (ß #_"bool" :m_handler_mode)

        (ß #_"u32" :m_start)

        (ß #_"s32" :m_inst_group)
        (ß #_"u32" :m_rd)
        (ß #_"u32" :m_rt)
        (ß #_"u32" :m_rm)
        (ß #_"u32" :m_rn)
        (ß #_"u32" :m_imm)
        (ß #_"u32" :m_cond)
        (ß #_"u32" :m_reglist)

        (when (ß size != 0)
            (ß #_"ram" mem = ram'new(base, size))

            (ß (:next mem) = (:m_ram this))
            (ß (:m_ram this) = mem)
        )

        (ß cpu''reset(this, base))
    )

    (defn #_"cpu" cpu''reset [#_"cpu" this, #_"u32" start]
        (§ for (#_"s32" i = 0; i < REGISTERS; i++)
            (ß (:m_regfile this)[i] = 0)
        )

        (ß (:m_apsr this) = 0)

        (ß (:m_start this) = start)

        ;; Fetch SP & boot PC from vector table
        (ß (:m_regfile this)[reg'SP] = cpu''read32(this, (:m_start this)))
        (ß (:m_regfile this)[reg'LR] = 0)
        (ß (:m_regfile this)[reg'PC] = cpu''read32(this, (:m_start this) + 4) & ~1)

        ;; Start in thread mode with main stack selected
        (ß (:m_msp this) = (:m_regfile this)[reg'SP])
        (ß (:m_psp this) = 0)
        (ß (:m_handler_mode this) = false)
        ;; (SPSEL = 0, nPRIV = 0)
        (ß (:m_control this) = 0)
        (ß (:m_primask this) = 0)

        (ß (:m_ipsr this) = 0)
        (ß (:m_epsr this) = 0)
        this
    )

    (defn #_"cpu" cpu''step [#_"cpu" this]
        (when (ß ((:m_regfile this)[reg'PC] & EXC_RETURN) == EXC_RETURN)
            (ß armv6m_exc_return(this, (:m_regfile this)[reg'PC]))
        )

        (ß #_"u16" inst = armv6m_read_inst(this, (:m_regfile this)[reg'PC]))

        (ß #_"u16" inst2)
        (if (ß armv6m_decode(this, inst))
            (ß inst2 = armv6m_read_inst(this, (:m_regfile this)[reg'PC] + 2))
            (ß inst2 = 0)
        )

        (ß armv6m_execute(this, inst, inst2))
        this
    )

    (defn #_"u16" armv6m_read_inst [#_"cpu" this, #_"u32" addr]
        (if (ß addr & 0x2)
            (§ return (cpu''read32(this, addr) >> 16) & 0xffff)
            (§ return (cpu''read32(this, addr) >> 0) & 0xffff)
        )
    )

    (defn #_"void" armv6m_update_sp [#_"cpu" this, #_"u32" sp]
        (ß (:m_regfile this)[reg'SP] = sp)

        (if (ß ((:m_control this) & CONTROL_SPSEL) && !(:m_handler_mode this))
            (ß (:m_psp this) = sp)
            (ß (:m_msp this) = sp)
        )
        nil
    )

    (defn #_"void" armv6m_update_n_z_flags [#_"cpu" this, #_"u32" rd]
        ;; Zero
        (if (ß rd == 0)
            (ß (:m_apsr this) |= APSR_Z)
            (ß (:m_apsr this) &= ~APSR_Z)
        )

        ;; Negative
        (if (ß rd & 0x80000000)
            (ß (:m_apsr this) |= APSR_N)
            (ß (:m_apsr this) &= ~APSR_N)
        )
        nil
    )

    (defn #_"u32" armv6m_add_with_carry [#_"cpu" this, #_"u32" rn, #_"u32" rm, #_"u32" carry_in, #_"u32" mask]
        (ß #_"u32" res = rn + rm + carry_in)

        ;; Zero
        (when (ß mask & APSR_Z)
            (if (ß (res & 0xffffffff) == 0)
                (ß (:m_apsr this) |= APSR_Z)
                (ß (:m_apsr this) &= ~APSR_Z)
            )
        )

        ;; Negative
        (when (ß mask & APSR_N)
            (if (ß res & 0x80000000)
                (ß (:m_apsr this) |= APSR_N)
                (ß (:m_apsr this) &= ~APSR_N)
            )
        )

        ;; Carry
        (when (ß mask & APSR_C)
            (ß #_"u64" unsigned_sum = (#_"u64")rn + (#_"u64")rm + carry_in)
            (if (ß unsigned_sum == (#_"u64")res)
                (ß (:m_apsr this) &= ~APSR_C)
                (ß (:m_apsr this) |= APSR_C)
            )
        )

        ;; Overflow
        (when (ß mask & APSR_V)
            (ß int64_t signed_sum = (int64_t)(int32_t)rn + (int64_t)(int32_t)rm + carry_in)
            (if (ß signed_sum == (int64_t)(int32_t)res)
                (ß (:m_apsr this) &= ~APSR_V)
                (ß (:m_apsr this) |= APSR_V)
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
                (ß (:m_apsr this) |= APSR_C)
                (ß (:m_apsr this) &= ~APSR_C)
            )
        )

        ;; Zero
        (if (ß (res & 0xffffffff) == 0)
            (ß (:m_apsr this) |= APSR_Z)
            (ß (:m_apsr this) &= ~APSR_Z)
        )

        ;; Negative
        (if (ß res & 0x80000000)
            (ß (:m_apsr this) |= APSR_N)
            (ß (:m_apsr this) &= ~APSR_N)
        )

        (§ return (#_"u32")res)
    )

    (defn #_"u32" armv6m_shift_right [#_"cpu" this, #_"u32" val, #_"u32" shift, #_"u32" mask]
        (ß #_"u32" res = (shift >= 32) ? 0 : val)

        ;; Carry Out (val[shift-1])
        (when (ß (mask & APSR_C) && (shift > 0))
            ;; Last lost bit shifted right
            (if (ß (val & (1 << (shift - 1))) && (shift <= 32))
                (ß (:m_apsr this) |= APSR_C)
                (ß (:m_apsr this) &= ~APSR_C)
            )
        )

        (ß res >>= shift)

        ;; Zero
        (if (ß (res & 0xffffffff) == 0)
            (ß (:m_apsr this) |= APSR_Z)
            (ß (:m_apsr this) &= ~APSR_Z)
        )

        ;; Negative
        (if (ß res & 0x80000000)
            (ß (:m_apsr this) |= APSR_N)
            (ß (:m_apsr this) &= ~APSR_N)
        )

        (§ return res)
    )

    (defn #_"u32" armv6m_arith_shift_right [#_"cpu" this, #_"u32" val, #_"u32" shift, #_"u32" mask]
        (ß signed #_"s32" res = val)

        ;; Carry Out (val[shift-1])
        (when (ß (mask & APSR_C) && (shift > 0))
            ;; Last lost bit shifted right
            (if (ß val & (1 << (shift - 1)))
                (ß (:m_apsr this) |= APSR_C)
                (ß (:m_apsr this) &= ~APSR_C)
            )
        )

        (ß res >>= shift)

        ;; Zero
        (if (ß (res & 0xffffffff) == 0)
            (ß (:m_apsr this) |= APSR_Z)
            (ß (:m_apsr this) &= ~APSR_Z)
        )

        ;; Negative
        (if (ß res & 0x80000000)
            (ß (:m_apsr this) |= APSR_N)
            (ß (:m_apsr this) &= ~APSR_N)
        )

        (§ return res)
    )

    (defn #_"u32" armv6m_rotate_right [#_"cpu" this, #_"u32" val, #_"u32" shift, #_"u32" mask]
        (ß #_"u32" res)

        (if (ß shift == 0)
            (ß res = val)
            (do
                (ß shift &= 0x1f)

                (ß res = val >> shift)
                (ß res |= (val << (32 - shift)))
            )
        )

        ;; Carry out
        (if (ß res & 0x80000000)
            (ß (:m_apsr this) |= APSR_C)
            (ß (:m_apsr this) &= ~APSR_C)
        )

        ;; Zero
        (if (ß (res & 0xffffffff) == 0)
            (ß (:m_apsr this) |= APSR_Z)
            (ß (:m_apsr this) &= ~APSR_Z)
        )

        ;; Negative
        (if (ß res & 0x80000000)
            (ß (:m_apsr this) |= APSR_N)
            (ß (:m_apsr this) &= ~APSR_N)
        )

        (§ return res)
    )

    (defn #_"u32" armv6m_sign_extend [#_"cpu" this, #_"u32" val, #_"s32" offset]
        (if (ß val & (1 << (offset - 1)))
            (ß val |= (~0) << offset)
            (ß val &= ~((~0) << offset))
        )

        (§ return val)
    )

    (defn #_"u32" armv6m_exception [#_"cpu" this, #_"u32" pc, #_"u32" exception]
        (ß #_"u32" sp)

        ;; Retrieve shadow stack pointer (depending on mode)
        (if (ß ((:m_control this) & CONTROL_SPSEL) && !(:m_handler_mode this))
            (ß sp = (:m_psp this))
            (ß sp = (:m_msp this))
        )

        ;; Push frame onto current stack
        (ß sp = sp - 4)
        (ß cpu''write32(this, sp, (:m_apsr this)))
        (ß sp = sp - 4)
        (ß cpu''write32(this, sp, (:m_regfile this)[reg'PC]))
        (ß sp = sp - 4)
        (ß cpu''write32(this, sp, (:m_regfile this)[reg'LR]))
        (ß sp = sp - 4)
        (ß cpu''write32(this, sp, (:m_regfile this)[12]))
        (ß sp = sp - 4)
        (ß cpu''write32(this, sp, (:m_regfile this)[3]))
        (ß sp = sp - 4)
        (ß cpu''write32(this, sp, (:m_regfile this)[2]))
        (ß sp = sp - 4)
        (ß cpu''write32(this, sp, (:m_regfile this)[1]))
        (ß sp = sp - 4)
        (ß cpu''write32(this, sp, (:m_regfile this)[0]))
        (ß (:m_regfile this)[reg'SP] = sp)

        ;; Record exception
        (ß (:m_ipsr this) = exception & 0x3f)

        ;; Fetch exception vector address into PC
        (ß (:m_regfile this)[reg'PC] = cpu''read32(this, (:m_start this) + (exception * 4)) & ~1)

        (if (ß (:m_handler_mode this))
            (do
                ;; LR = Return to handler mode (recursive interrupt?)
                (ß (:m_regfile this)[reg'LR] = 0xfffffff1)
            )
            (if (ß ((:m_control this) & CONTROL_SPSEL) == 0)
                (do
                    ;; LR = Return to thread mode (with main stack)
                    (ß (:m_regfile this)[reg'LR] = 0xfffffff9)
                )
                (do
                    ;; LR = Return to thread mode (with process stack)
                    (ß (:m_regfile this)[reg'LR] = 0xfffffffd)
                )
            )
        )

        ;; Swap to handler mode
        (ß (:m_handler_mode this) = true)

        ;; Current stack is now main
        (ß (:m_control this) &= ~CONTROL_SPSEL)

        (§ return (:m_regfile this)[reg'PC])
    )

    (defn #_"void" armv6m_exc_return [#_"cpu" this, #_"u32" pc]
        (when (ß !(:m_handler_mode this))
            (§ return nil)
        )

        (when (ß (pc & EXC_RETURN) == EXC_RETURN)
            ;; TODO: Should be 0x1f...
            (§ switch (pc & 0xf)
                (§ case 0x1)
                (§
                    (ß (:m_handler_mode this) = true)
                    (ß (:m_control this) &= ~CONTROL_SPSEL)
                    (§ break)
                )
                (§ case 0x9)
                (§
                    (ß (:m_handler_mode this) = false)
                    (ß (:m_control this) &= ~CONTROL_SPSEL)
                    (§ break)
                )
                (§ case 0xd)
                (§
                    (ß (:m_handler_mode this) = false)
                    (ß (:m_control this) |= CONTROL_SPSEL)
                    (§ break)
                )
                (§ default)
                (§
                    (ß assert(!"Not handled"))
                    (§ break)
                )
            )

            (ß #_"u32" sp = (:m_regfile this)[reg'SP])
            (ß (:m_regfile this)[0] = cpu''read32(this, sp))
            (ß sp = sp + 4)
            (ß (:m_regfile this)[1] = cpu''read32(this, sp))
            (ß sp = sp + 4)
            (ß (:m_regfile this)[2] = cpu''read32(this, sp))
            (ß sp = sp + 4)
            (ß (:m_regfile this)[3] = cpu''read32(this, sp))
            (ß sp = sp + 4)
            (ß (:m_regfile this)[12] = cpu''read32(this, sp))
            (ß sp = sp + 4)
            (ß (:m_regfile this)[reg'LR] = cpu''read32(this, sp))
            (ß sp = sp + 4)
            (ß (:m_regfile this)[reg'PC] = cpu''read32(this, sp))
            (ß sp = sp + 4)
            (ß (:m_apsr this) = cpu''read32(this, sp))
            (ß sp = sp + 4)
            (ß armv6m_update_sp(this, sp))
        )
        nil
    )

    (defn #_"bool" armv6m_decode [#_"cpu" this, #_"u16" inst]
        (ß #_"bool" res = false)
        (ß #_"bool" v_decoded = false)

        (ß (:m_rd this) = 0)
        (ß (:m_rt this) = 0)
        (ß (:m_rm this) = 0)
        (ß (:m_rn this) = 0)
        (ß (:m_imm this) = 0)
        (ß (:m_reglist this) = 0)
        (ß (:m_cond this) = 0)

        ;; Group 0?
        (when (ß !v_decoded)
            (ß v_decoded = true)
            (ß (:m_inst_group this) = code'IGRP0)
            (§ switch (inst & mask'IGRP0)
                #_"BCC <label>"
                #_"1 1 0 1 cond imm8"
                (§ case code'BCC)
                (§
                    (ß (:m_cond this) = (inst >> 8) & 0x0f)
                    (ß (:m_imm this) = (inst >> 0) & 0xff)
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
            (ß (:m_inst_group this) = code'IGRP1)
            (§ switch (inst & mask'IGRP1)
                #_"ADDS <Rdn>,#<imm8>"
                #_"0 0 1 1 0 Rdn imm8"
                (§ case code'ADDS_1)
                #_"SUBS <Rdn>,#<imm8>"
                #_"0 0 1 11 Rdn imm8"
                (§ case code'SUBS_1)
                (§
                    (ß (:m_rd this) = (inst >> 8) & 0x7)
                    (ß (:m_rn this) = (:m_rd this))
                    (ß (:m_imm this) = (inst >> 0) & 0xff)
                    (§ break)
                )

                #_"ADR <Rd>,<label>"
                #_"1 0 1 0 0 Rd imm8"
                (§ case code'ADR)
                #_"MOVS <Rd>,#<imm8>"
                #_"0 0 1 0 0 Rd imm8"
                (§ case code'MOVS)
                (§
                    (ß (:m_rd this) = (inst >> 8) & 0x7)
                    (ß (:m_imm this) = (inst >> 0) & 0xff)
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
                    (ß (:m_imm this) = (inst >> 6) & 0x1f)
                    (ß (:m_rm this) = (inst >> 3) & 0x7)
                    (ß (:m_rd this) = (inst >> 0) & 0x7)
                    (§ break)
                )

                #_"B <label>"
                #_"1 1 1 0 0 imm11"
                (§ case code'B)
                (§
                    (ß (:m_imm this) = (inst >> 0) & 0x7ff)
                    (§ break)
                )

                #_"BL <label>"
                #_"1 1 1 01 S imm10 1 1 J1 1 J2 imm11"
                (§ case code'BL)
                (§
                    ;; 32-bit instruction
                    (ß res = true)
                    (ß (:m_imm this) = (inst >> 0) & 0x7ff)
                    (ß (:m_rd this) = reg'LR)

                    ;; TODO: Clean this up
                    ;; Check next instruction to work out if this is a BL or MSR
                    (when (ß (armv6m_read_inst(this, (:m_regfile this)[reg'PC] + 2) & 0xc000) != 0xc000)
                        (ß v_decoded = false)
                    )
                    (§ break)
                )

                #_"CMP <Rn>,#<imm8>"
                #_"0 0 1 0 1 Rn imm8"
                (§ case code'CMP)
                (§
                    (ß (:m_rn this) = (inst >> 8) & 0x7)
                    (ß (:m_imm this) = (inst >> 0) & 0xff)
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
                    (ß (:m_rn this) = (inst >> 8) & 0x7)
                    (ß (:m_rd this) = (:m_rn this))
                    (ß (:m_reglist this) = (inst >> 0) & 0xff)
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
                    (ß (:m_imm this) = (inst >> 6) & 0x1f)
                    (ß (:m_rn this) = (inst >> 3) & 0x7)
                    (ß (:m_rt this) = (inst >> 0) & 0x7)
                    (ß (:m_rd this) = (:m_rt this))
                    (§ break)
                )

                #_"LDR <Rt>,<label>"
                #_"0 1 0 0 1 Rt imm8"
                (§ case code'LDR_2)
                (§
                    (ß (:m_rt this) = (inst >> 8) & 0x7)
                    (ß (:m_rd this) = (:m_rt this))
                    (ß (:m_imm this) = (inst >> 0) & 0xff)
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
                    (ß (:m_rt this) = (inst >> 8) & 0x7)
                    (ß (:m_rn this) = reg'SP)
                    (ß (:m_rd this) = (:m_rt this))
                    (ß (:m_imm this) = (inst >> 0) & 0xff)
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
            (ß (:m_inst_group this) = code'IGRP2)
            (§ switch (inst & mask'IGRP2)
                #_"ADDS <Rd>,<Rn>,#<imm3>"
                #_"0 0 0 1 1 1 0 imm3 Rn Rd"
                (§ case code'ADDS)
                #_"SUBS <Rd>,<Rn>,#<imm3>"
                #_"0 0 0 11 1 1 imm3 Rn Rd"
                (§ case code'SUBS)
                (§
                    (ß (:m_imm this) = (inst >> 6) & 0x7)
                    (ß (:m_rn this) = (inst >> 3) & 0x7)
                    (ß (:m_rd this) = (inst >> 0) & 0x7)
                    (§ break)
                )

                #_"ADDS <Rd>,<Rn>,<Rm>"
                #_"0 0 0 1 1 0 0 Rm Rn Rd"
                (§ case code'ADDS_2)
                #_"SUBS <Rd>,<Rn>,<Rm>"
                #_"0 0 0 11 0 1 Rm Rn Rd"
                (§ case code'SUBS_2)
                (§
                    (ß (:m_rm this) = (inst >> 6) & 0x7)
                    (ß (:m_rn this) = (inst >> 3) & 0x7)
                    (ß (:m_rd this) = (inst >> 0) & 0x7)
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
                    (ß (:m_rm this) = (inst >> 6) & 0x7)
                    (ß (:m_rn this) = (inst >> 3) & 0x7)
                    (ß (:m_rt this) = (inst >> 0) & 0x7)
                    (ß (:m_rd this) = (:m_rt this))
                    (§ break)
                )

                #_"POP <registers>"
                #_"1 0 1 1 1 1 0 P register_list"
                (§ case code'POP)
                (§
                    (ß (:m_reglist this) = (inst >> 0) & 0xff)
                    (when (ß inst & (1 << 8))
                        (ß (:m_reglist this) |= (1 << reg'PC))
                    )
                    (§ break)
                )

                #_"PUSH <registers>"
                #_"1 0 1 1 0 1 0 M register_list"
                (§ case code'PUSH)
                (§
                    (ß (:m_reglist this) = (inst >> 0) & 0xff)
                    (when (ß inst & (1 << 8))
                        (ß (:m_reglist this) |= (1 << reg'LR))
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
            (ß (:m_inst_group this) = code'IGRP3)
            (§ switch (inst & mask'IGRP3)
                #_"ADD <Rdn>,<Rm>"
                #_"0 1 0 0 0 1 0 0 Rm Rdn"
                (§ case code'ADD)
                (§
                    (ß (:m_rm this) = (inst >> 3) & 0xf)
                    (ß (:m_rd this) = (inst >> 0) & 0x7)
                    (ß (:m_rd this) |= (inst >> 4) & 0x8)
                    (ß (:m_rn this) = (:m_rd this))
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
                    (ß (:m_imm this) = (inst >> 0) & 0xff)
                    (§ break)
                )

                #_"CMP <Rn>,<Rm> <Rn> and <Rm> not both from R0-R7"
                #_"0 1 0 0 0 1 0 1 N Rm Rn"
                (§ case code'CMP_2)
                (§
                    (ß (:m_rm this) = (inst >> 3) & 0xf)
                    (ß (:m_rn this) = (inst >> 0) & 0x7)
                    (ß (:m_rn this) |= (inst >> 4) & 0x8)
                    (§ break)
                )

                #_"MOV <Rd>,<Rm> Otherwise all versions of the Thumb instruction set."
                #_"0 1 0 0 0 1 1 0 D Rm Rd"
                (§ case code'MOV)
                (§
                    (ß (:m_rm this) = (inst >> 3) & 0xf)
                    (ß (:m_rd this) = (inst >> 0) & 0x7)
                    (ß (:m_rd this) |= (inst >> 4) & 0x8)
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
            (ß (:m_inst_group this) = code'IGRP4)
            (§ switch (inst & mask'IGRP4)
                #_"ADD SP,SP,#<imm7>"
                #_"1 0 1 1 0 0 0 0 0 imm7"
                (§ case code'ADD_2)
                #_"SUB SP,SP,#<imm7>"
                #_"1 0 1 1 000 0 1 imm7"
                (§ case code'SUB)
                (§
                    (ß (:m_rn this) = reg'SP)
                    (ß (:m_rd this) = reg'SP)
                    (ß (:m_imm this) = (inst >> 0) & 0x7f)
                    (§ break)
                )

                #_"BLX <Rm>"
                #_"0 1 0 0 0 1 1 1 1 Rm (0) (0) (0)"
                (§ case code'BLX)
                (§
                    (ß (:m_rm this) = (inst >> 3) & 0xf)
                    (ß (:m_rd this) = reg'LR)
                    (§ break)
                )

                #_"BX <Rm>"
                #_"0 1 0 0 0 1 1 1 0 Rm (0) (0) (0)"
                (§ case code'BX)
                (§
                    (ß (:m_rm this) = (inst >> 3) & 0xf)
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
            (ß (:m_inst_group this) = code'IGRP5)
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
                    (ß (:m_rm this) = (inst >> 3) & 0x7)
                    (ß (:m_rd this) = (inst >> 0) & 0x7)
                    (ß (:m_rn this) = (:m_rd this))
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
                    (ß (:m_rm this) = (inst >> 3) & 0x7)
                    (ß (:m_rn this) = (inst >> 0) & 0x7)
                    (§ break)
                )

                #_"MULS <Rdm>,<Rn>,<Rdm>"
                #_"0 1 0 0 0 0 1 1 0 1 Rn Rdm"
                (§ case code'MULS)
                (§
                    (ß (:m_rn this) = (inst >> 3) & 0x7)
                    (ß (:m_rd this) = (inst >> 0) & 0x7)
                    (ß (:m_rm this) = (:m_rd this))
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
                    (ß (:m_rm this) = (inst >> 3) & 0x7)
                    (ß (:m_rd this) = (inst >> 0) & 0x7)
                    (§ break)
                )

                #_"RSBS <Rd>,<Rn>,#0"
                #_"0 1 0 0 0 0 1 0 0 1 Rn Rd"
                (§ case code'RSBS)
                (§
                    (ß (:m_rn this) = (inst >> 3) & 0x7)
                    (ß (:m_rd this) = (inst >> 0) & 0x7)
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
            (ß (:m_inst_group this) = code'IGRP6)
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
                    (ß (:m_rn this) = (inst >> 0) & 0xf)

                    ;; 32-bit instruction
                    (ß res = true)
                    (§ break)
                )
                #_"CPS<effect> i"
                #_"1 0 1 1 0 1 1 0 0 1 1 im (0) (0) (1) (0)"
                (§ case code'CPS)
                (§
                    (ß (:m_imm this) = (inst >> 4) & 0x1)
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
            (ß (:m_inst_group this) = code'IGRP7)
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
            (ß (:m_inst_group this) = code'IGRP8)
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
        (ß #_"u32" reg_rm = (:m_regfile this)[(:m_rm this)])
        (ß #_"u32" reg_rn = (:m_regfile this)[(:m_rn this)])
        (ß #_"u32" reg_rd = 0)
        (ß #_"u32" pc = (:m_regfile this)[reg'PC])
        (ß #_"u32" offset = 0)
        (ß #_"bool" write_rd = false)

        (ß pc = pc + 2)

        (§ switch ((:m_inst_group this))
            (§ case code'IGRP0)
            (§
                (§ switch (inst & mask'IGRP0)
                    #_"BCC <label>"
                    #_"1 1 0 1 cond imm8"
                    (§ case code'BCC)
                    (§
                        ;; Sign extend offset
                        (ß offset = armv6m_sign_extend(this, (:m_imm this), 8))

                        ;; Convert to words
                        (ß offset = offset << 1)

                        ;; Make relative to PC + 4
                        (ß offset = offset + pc + 2)

                        (§ switch ((:m_cond this))
                            (§ case 0) #_"EQ"
                            (§
                                (when (ß (:m_apsr this) & APSR_Z)
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 1) #_"NE"
                            (§
                                (when (ß ((:m_apsr this) & APSR_Z) == 0)
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 2) #_"CS/HS"
                            (§
                                (when (ß (:m_apsr this) & APSR_C)
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 3) #_"CC/LO"
                            (§
                                (when (ß ((:m_apsr this) & APSR_C) == 0)
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 4) #_"MI"
                            (§
                                (when (ß (:m_apsr this) & APSR_N)
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 5) #_"PL"
                            (§
                                (when (ß ((:m_apsr this) & APSR_N) == 0)
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 6) #_"VS"
                            (§
                                (when (ß (:m_apsr this) & APSR_V)
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 7) #_"VC"
                            (§
                                (when (ß ((:m_apsr this) & APSR_V) == 0)
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 8) #_"HI"
                            (§
                                (when (ß ((:m_apsr this) & APSR_C) && (((:m_apsr this) & APSR_Z) == 0))
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 9) #_"LS"
                            (§
                                (when (ß (((:m_apsr this) & APSR_C) == 0) || ((:m_apsr this) & APSR_Z))
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 10) #_"GE"
                            (§
                                (when (ß (((:m_apsr this) & APSR_N) >> APSR_N_SHIFT) == (((:m_apsr this) & APSR_V) >> APSR_V_SHIFT))
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 11) #_"LT"
                            (§
                                (when (ß (((:m_apsr this) & APSR_N) >> APSR_N_SHIFT) != (((:m_apsr this) & APSR_V) >> APSR_V_SHIFT))
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 12) #_"GT"
                            (§
                                (when (ß (((:m_apsr this) & APSR_Z) == 0) && ((((:m_apsr this) & APSR_N) >> APSR_N_SHIFT) == (((:m_apsr this) & APSR_V) >> APSR_V_SHIFT)))
                                    (ß pc = offset)
                                )
                                (§ break)
                            )
                            (§ case 13) #_"LE"
                            (§
                                (when (ß ((:m_apsr this) & APSR_Z) || ((((:m_apsr this) & APSR_N) >> APSR_N_SHIFT) != (((:m_apsr this) & APSR_V) >> APSR_V_SHIFT)))
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
                        (ß reg_rd = armv6m_add_with_carry(this, reg_rn, (:m_imm this), 0, ALL_FLAGS))
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"ADD <Rd>,SP,#<imm8>"
                    #_"1 0 1 0 1 Rd imm8"
                    (§ case code'ADD_1)
                    (§
                        (ß reg_rd = reg_rn + ((:m_imm this) << 2))
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"ADR <Rd>,<label>"
                    #_"1 0 1 0 0 Rd imm8"
                    (§ case code'ADR)
                    (§
                        (ß reg_rd = pc + (:m_imm this) + 2)
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"ASRS <Rd>,<Rm>,#<imm5>"
                    #_"0 0 0 1 0 imm5 Rm Rd"
                    (§ case code'ASRS)
                    (§
                        (when (ß (:m_imm this) == 0)
                            (ß (:m_imm this) = 32)
                        )

                        (ß reg_rd = armv6m_arith_shift_right(this, reg_rm, (:m_imm this), FLAGS_NZC))
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"B <label>"
                    #_"1 1 1 0 0 imm11"
                    (§ case code'B)
                    (§
                        ;; Sign extend offset
                        (ß offset = armv6m_sign_extend(this, (:m_imm this), 11))

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
                        (ß offset = armv6m_sign_extend(this, (:m_imm this), 11))
                        (ß offset <<= 11)

                        ;; Additional range
                        (ß (:m_imm this) = (inst2 >> 0) & 0x7ff)
                        (ß offset |= (:m_imm this))

                        ;; Make relative to PC
                        (ß offset <<= 1)
                        (ß offset = offset + pc)

                        ;; (:m_rd this) = reg'LR
                        (ß reg_rd = (pc + 2) | 1)
                        (ß write_rd = true)

                        (ß pc = offset + 2)
                        (§ break)
                    )
                    #_"CMP <Rn>,#<imm8>"
                    #_"0 0 1 0 1 Rn imm8"
                    (§ case code'CMP)
                    (§
                        (ß reg_rd = armv6m_add_with_carry(this, reg_rn, ~(:m_imm this), 1, ALL_FLAGS))
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
                        (§ for (#_"s32" i = 0; i < REGISTERS && (:m_reglist this) != 0; i++)
                            (when (ß (:m_reglist this) & (1 << i))
                                (ß (:m_regfile this)[i] = cpu''read32(this, reg_rn))
                                (when (ß i == reg'PC)
                                    (when (ß ((:m_regfile this)[i] & EXC_RETURN) != EXC_RETURN)
                                        (ß (:m_regfile this)[i] &= ~1)
                                    )
                                    (ß pc = (:m_regfile this)[i])
                                )
                                (ß reg_rn = reg_rn + 4)
                                (ß (:m_reglist this) &= ~(1 << i))
                            )
                        )

                        (ß (:m_regfile this)[(:m_rd this)] = reg_rn)
                        (ß assert((:m_rd this) != reg'PC))
                        (§ break)
                    )
                    #_"LDR <Rt>, [<Rn>{,#<imm5>}]"
                    #_"0 1 1 0 1 imm5 Rn Rt"
                    (§ case code'LDR)
                    (§
                        (ß (:m_regfile this)[(:m_rt this)] = cpu''read32(this, reg_rn + ((:m_imm this) << 2)))
                        (ß assert((:m_rd this) != reg'PC))
                        (§ break)
                    )
                    #_"LDR <Rt>,[SP{,#<imm8>}]"
                    #_"1 0 0 1 1 Rt imm8"
                    (§ case code'LDR_1)
                    (§
                        (ß (:m_regfile this)[(:m_rt this)] = cpu''read32(this, reg_rn + ((:m_imm this) << 2)))
                        (ß assert((:m_rd this) != reg'PC))
                        (§ break)
                    )
                    #_"LDR <Rt>,<label>"
                    #_"0 1 0 0 1 Rt imm8"
                    (§ case code'LDR_2)
                    (§
                        (ß (:m_regfile this)[(:m_rt this)] = cpu''read32(this, ((:m_regfile this)[reg'PC] & 0xfffffffc) + ((:m_imm this) << 2) + 4))
                        (ß assert((:m_rd this) != reg'PC))
                        (§ break)
                    )
                    #_"LDRB <Rt>,[<Rn>{,#<imm5>}]"
                    #_"0 1 1 1 1 imm5 Rn Rt"
                    (§ case code'LDRB)
                    (§
                        (ß (:m_regfile this)[(:m_rt this)] = cpu''read8(this, reg_rn + (:m_imm this)))
                        (§ break)
                    )
                    #_"LDRH <Rt>,[<Rn>{,#<imm5>}]"
                    #_"1 0 0 0 1 imm5 Rn Rt"
                    (§ case code'LDRH)
                    (§
                        (ß (:m_regfile this)[(:m_rt this)] = cpu''read16(this, reg_rn + ((:m_imm this) << 1)))
                        (§ break)
                    )
                    #_"LSLS <Rd>,<Rm>,#<imm5>"
                    #_"0 0 0 0 0 imm5 Rm Rd"
                    #_"MOVS <Rd>,<Rm>"
                    #_"0 0 0 0 0 0 0 0 0 0 Rm Rd"
                 ;; case code'MOVS_1:
                    (§ case code'LSLS)
                    (§
                        (if (ß (:m_imm this) == 0)
                            (do
                                ;; MOVS <Rd>,<Rm>
                                (ß reg_rd = reg_rm)
                                (ß write_rd = true)

                                ;; Update N & Z
                                (ß armv6m_update_n_z_flags(this, reg_rd))
                            )
                            (do
                                ;; LSLS <Rd>,<Rm>,#<imm5>
                                (ß reg_rd = armv6m_shift_left(this, reg_rm, (:m_imm this), FLAGS_NZC))
                                (ß write_rd = true)
                            )
                        )
                        (§ break)
                    )
                    #_"LSRS <Rd>,<Rm>,#<imm5>"
                    #_"0 0 0 0 1 imm5 Rm Rd"
                    (§ case code'LSRS)
                    (§
                        (when (ß (:m_imm this) == 0)
                            (ß (:m_imm this) = 32)
                        )

                        (ß reg_rd = armv6m_shift_right(this, reg_rm, (:m_imm this), FLAGS_NZC))
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"MOVS <Rd>,#<imm8>"
                    #_"0 0 1 0 0 Rd imm8"
                    (§ case code'MOVS)
                    (§
                        (ß reg_rd = (:m_imm this))
                        (ß write_rd = true)

                        (ß armv6m_update_n_z_flags(this, reg_rd))
                        (§ break)
                    )
                    #_"STM <Rn>!,<registers>"
                    #_"1 1 0 0 0 Rn register_list"
                    (§ case code'STM)
                    (§
                        (ß #_"u32" addr = reg_rn)

                        (§ for (#_"s32" i = 0; i < REGISTERS && (:m_reglist this) != 0; i++)
                            (when (ß (:m_reglist this) & (1 << i))
                                (ß cpu''write32(this, addr, (:m_regfile this)[i]))
                                (ß addr = addr + 4)
                                (ß (:m_reglist this) &= ~(1 << i))
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
                        (ß cpu''write32(this, reg_rn + ((:m_imm this) << 2), (:m_regfile this)[(:m_rt this)]))
                        (§ break)
                    )
                    #_"STR <Rt>,[SP,#<imm8>]"
                    #_"1 0 0 1 0 Rt imm8"
                    (§ case code'STR_1)
                    (§
                        (ß cpu''write32(this, reg_rn + ((:m_imm this) << 2), (:m_regfile this)[(:m_rt this)]))
                        (§ break)
                    )
                    #_"STRB <Rt>,[<Rn>,#<imm5>]"
                    #_"0 1 1 1 0 imm5 Rn Rt"
                    (§ case code'STRB)
                    (§
                        (ß cpu''write8(this, reg_rn + (:m_imm this), (:m_regfile this)[(:m_rt this)]))
                        (§ break)
                    )
                    #_"STRH <Rt>,[<Rn>{,#<imm5>}]"
                    #_"1 0 0 0 0 imm5 Rn Rt"
                    (§ case code'STRH)
                    (§
                        (ß cpu''write16(this, reg_rn + ((:m_imm this) << 1), (:m_regfile this)[(:m_rt this)]))
                        (§ break)
                    )
                    #_"SUBS <Rdn>,#<imm8>"
                    #_"0 0 1 11 Rdn imm8"
                    (§ case code'SUBS_1)
                    (§
                        (ß reg_rd = armv6m_add_with_carry(this, reg_rn, ~(:m_imm this), 1, ALL_FLAGS))
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
                        (ß reg_rd = armv6m_add_with_carry(this, reg_rn, (:m_imm this), 0, ALL_FLAGS))
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
                        (ß (:m_regfile this)[(:m_rt this)] = cpu''read32(this, reg_rn + reg_rm))
                        (ß assert((:m_rt this) != reg'PC))
                        (§ break)
                    )
                    #_"LDRB <Rt>,[<Rn>,<Rm>]"
                    #_"0 1 0 1 1 1 0 Rm Rn Rt"
                    (§ case code'LDRB_1)
                    (§
                        (ß (:m_regfile this)[(:m_rt this)] = cpu''read8(this, reg_rn + reg_rm))
                        (§ break)
                    )
                    #_"LDRH <Rt>,[<Rn>,<Rm>]"
                    #_"0 1 0 1 1 0 1 Rm Rn Rt"
                    (§ case code'LDRH_1)
                    (§
                        (ß (:m_regfile this)[(:m_rt this)] = cpu''read16(this, reg_rn + reg_rm))
                        (§ break)
                    )
                    #_"LDRSB <Rt>,[<Rn>,<Rm>]"
                    #_"0 1 0 1 0 1 1 Rm Rn Rt"
                    (§ case code'LDRSB)
                    (§
                        (ß reg_rd = cpu''read8(this, reg_rn + reg_rm))
                        (ß (:m_regfile this)[(:m_rt this)] = armv6m_sign_extend(this, reg_rd, 8))
                        (§ break)
                    )
                    #_"LDRSH <Rt>,[<Rn>,<Rm>]"
                    #_"0 1 0 1 1 1 1 Rm Rn Rt"
                    (§ case code'LDRSH)
                    (§
                        (ß reg_rd = cpu''read16(this, reg_rn + reg_rm))
                        (ß (:m_regfile this)[(:m_rt this)] = armv6m_sign_extend(this, reg_rd, 16))
                        (§ break)
                    )
                    #_"POP <registers>"
                    #_"1 0 1 1 1 1 0 P register_list"
                    (§ case code'POP)
                    (§
                        (ß #_"u32" sp = (:m_regfile this)[reg'SP])

                        (§ for (#_"s32" i = 0; i < REGISTERS && (:m_reglist this) != 0; i++)
                            (when (ß (:m_reglist this) & (1 << i))
                                (ß (:m_regfile this)[i] = cpu''read32(this, sp))

                                (ß sp = sp + 4)

                                (when (ß i == reg'PC)
                                    (when (ß ((:m_regfile this)[i] & EXC_RETURN) != EXC_RETURN)
                                        (ß (:m_regfile this)[i] &= ~1)
                                    )
                                    (ß pc = (:m_regfile this)[i])
                                )

                                (ß (:m_reglist this) &= ~(1 << i))
                            )
                        )

                        (ß armv6m_update_sp(this, sp))
                        (§ break)
                    )
                    #_"PUSH <registers>"
                    #_"1 0 1 1 0 1 0 M register_list"
                    (§ case code'PUSH)
                    (§
                        (ß #_"u32" sp = (:m_regfile this)[reg'SP])
                        (ß #_"u32" addr = sp)
                        (ß #_"s32" bits_set = 0)

                        (§ for (#_"s32" i = 0; i < REGISTERS; i++)
                            (when (ß (:m_reglist this) & (1 << i))
                                (ß bits_set++)
                            )
                        )

                        (ß addr = addr - (4 * bits_set))

                        (§ for (#_"s32" i = 0; i < REGISTERS && (:m_reglist this) != 0; i++)
                            (when (ß (:m_reglist this) & (1 << i))
                                (ß cpu''write32(this, addr, (:m_regfile this)[i]))
                                (ß sp = sp - 4)
                                (ß addr = addr + 4)
                                (ß (:m_reglist this) &= ~(1 << i))
                            )
                        )

                        (ß armv6m_update_sp(this, sp))
                        (§ break)
                    )
                    #_"STR <Rt>,[<Rn>,<Rm>]"
                    #_"0 1 0 1 0 00 Rm Rn Rt"
                    (§ case code'STR_2)
                    (§
                        (ß cpu''write32(this, reg_rn + reg_rm, (:m_regfile this)[(:m_rt this)]))
                        (§ break)
                    )
                    #_"STRB <Rt>,[<Rn>,<Rm>]"
                    #_"0 1 0 1 0 1 0 Rm Rn Rt"
                    (§ case code'STRB_1)
                    (§
                        (ß cpu''write8(this, reg_rn + reg_rm, (:m_regfile this)[(:m_rt this)]))
                        (§ break)
                    )
                    #_"STRH <Rt>,[<Rn>,<Rm>]"
                    #_"0 1 0 1 0 0 1 Rm Rn Rt"
                    (§ case code'STRH_1)
                    (§
                        (ß cpu''write16(this, reg_rn + reg_rm, (:m_regfile this)[(:m_rt this)]))
                        (§ break)
                    )
                    #_"SUBS <Rd>,<Rn>,#<imm3>"
                    #_"0 0 0 11 1 1 imm3 Rn Rd"
                    (§ case code'SUBS)
                    (§
                        (ß reg_rd = armv6m_add_with_carry(this, reg_rn, ~(:m_imm this), 1, ALL_FLAGS))
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"SUBS <Rd>,<Rn>,<Rm>"
                    #_"0 0 0 11 0 1 Rm Rn Rd"
                    (§ case code'SUBS_2)
                    (§
                        (ß reg_rd = armv6m_add_with_carry(this, reg_rn, ~reg_rm, 1, ALL_FLAGS))
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
                        (ß reg_rd = armv6m_add_with_carry(this, reg_rn, ~reg_rm, 1, ALL_FLAGS))
                        (§ break)
                    )
                    #_"MOV <Rd>,<Rm> Otherwise all versions of the Thumb instruction set."
                    #_"0 1 0 0 0 1 1 0 D Rm Rd"
                    (§ case code'MOV)
                    (§
                        (if (ß (:m_rd this) == reg'PC)
                            (do
                                ;; Write to PC
                                (ß pc = reg_rm & ~1)

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
                        (ß reg_rd = reg_rn + ((:m_imm this) << 2))
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"BLX <Rm>"
                    #_"0 1 0 0 0 1 1 1 1 Rm (0) (0) (0)"
                    (§ case code'BLX)
                    (§
                        ;; (:m_rd this) = reg'LR
                        (ß reg_rd = pc | 1)
                        (ß write_rd = true)

                        (ß pc = reg_rm & ~1)
                        (§ break)
                    )
                    #_"BX <Rm>"
                    #_"0 1 0 0 0 1 1 1 0 Rm (0) (0) (0)"
                    (§ case code'BX)
                    (§
                        (ß pc = reg_rm & ~1)
                        (§ break)
                    )
                    #_"SUB SP,SP,#<imm7>"
                    #_"1 0 1 1 000 0 1 imm7"
                    (§ case code'SUB)
                    (§
                        (ß reg_rd = reg_rn - ((:m_imm this) << 2))
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
                        (ß reg_rd = armv6m_add_with_carry(this, reg_rn, reg_rm, ((:m_apsr this) & APSR_C) ? 1 : 0, ALL_FLAGS))
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
                        (ß reg_rd = reg_rn & (~reg_rm))
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
                        (ß reg_rd = armv6m_add_with_carry(this, reg_rn, ~reg_rm, 1, ALL_FLAGS))
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
                        (ß reg_rd = ~reg_rm)
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
                        (ß reg_rd = ((reg_rm >> 0) & 0xff) << 24)
                        (ß reg_rd |= ((reg_rm >> 8) & 0xff) << 16)
                        (ß reg_rd |= ((reg_rm >> 16) & 0xff) << 8)
                        (ß reg_rd |= ((reg_rm >> 24) & 0xff) << 0)
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"REV16 <Rd>,<Rm>"
                    #_"1 0 1 1 1 0 1 0 0 1 Rm Rd"
                    (§ case code'REV16)
                    (§
                        (ß reg_rd = ((reg_rm >> 0) & 0xff) << 8)
                        (ß reg_rd |= ((reg_rm >> 8) & 0xff) << 0)
                        (ß reg_rd |= ((reg_rm >> 16) & 0xff) << 24)
                        (ß reg_rd |= ((reg_rm >> 24) & 0xff) << 16)
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"REVSH <Rd>,<Rm>"
                    #_"1 0 1 1 1 0 1 0 1 1 Rm Rd"
                    (§ case code'REVSH)
                    (§
                        (ß reg_rd = ((reg_rm >> 0) & 0xff) << 8)
                        (ß reg_rd |= ((reg_rm >> 8) & 0xff) << 0)
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
                        (ß reg_rd = armv6m_add_with_carry(this, ~reg_rn, 0, 1, ALL_FLAGS))
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"SBCS <Rdn>,<Rm>"
                    #_"0 1 0 0 0 0 0 1 1 0 Rm Rdn"
                    (§ case code'SBCS)
                    (§
                        (ß reg_rd = armv6m_add_with_carry(this, reg_rn, ~reg_rm, ((:m_apsr this) & APSR_C) ? 1 : 0, ALL_FLAGS))
                        (ß write_rd = true)
                        (§ break)
                    )
                    #_"SXTB <Rd>,<Rm>"
                    #_"1 0 1 1 100 0 0 1 Rm Rd"
                    (§ case code'SXTB)
                    (§
                        (ß reg_rd = reg_rm & 0xff)
                        (when (ß reg_rd & 0x80)
                            (ß reg_rd |= (~0) << 8)
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
                            (ß reg_rd |= (~0) << 16)
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
                        (ß #_"u32" sysm = (inst2 >> 0) & 0xff)
                        (ß (:m_rd this) = (inst2 >> 8) & 0xf)

                        ;; Increment PC past second instruction word
                        (ß pc = pc + 2)

                        (§ switch ((sysm >> 3) & 0x1f)
                            (§ case 0)
                            (§
                                (ß #_"u32" val = 0)

                                (when (ß sysm & 0x1)
                                    (ß val |= (:m_ipsr this) & 0x1ff)
                                )

                                (when (ß !(sysm & 0x4))
                                    (ß val |= ((:m_apsr this) & 0xf8000000))
                                )

                                (ß val |= (:m_ipsr this))
                                (ß val |= (:m_epsr this))

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
                                        (ß reg_rd = (:m_msp this))
                                        (ß write_rd = true)
                                        (§ break)
                                    )
                                    (§ case 1)
                                    (§
                                        ;; Process SP
                                        (ß reg_rd = (:m_psp this))
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
                                        (ß reg_rd = (:m_primask this) & PRIMASK_PM)
                                        (ß write_rd = true)
                                        (§ break)
                                    )
                                    (§ case 4)
                                    (§
                                        ;; Control<1:0>
                                        (ß reg_rd = (:m_control this) & CONTROL_MASK)
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
                        (ß #_"u32" sysm = (inst2 >> 0) & 0xff)

                        ;; Increment PC past second instruction word
                        (ß pc = pc + 2)

                        (§ switch ((sysm >> 3) & 0x1f)
                            (§ case 0)
                            (§
                                (when (ß !(sysm & 0x4))
                                    (ß (:m_apsr this) = reg_rn & 0xf8000000)
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
                                        (ß (:m_msp this) = reg_rn)
                                        (§ break)
                                    )
                                    (§ case 1)
                                    (§
                                        ;; Process SP
                                        (ß (:m_psp this) = reg_rn)
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
                                        (ß (:m_primask this) = reg_rn & PRIMASK_PM)
                                        (§ break)
                                    )
                                    (§ case 4)
                                    (§
                                        ;; Control<1:0>
                                        (when (ß !(:m_handler_mode this))
                                            (ß (:m_control this) = reg_rn & CONTROL_MASK)

                                            ;; Allow switching of current SP
                                         ;; (if (ß (:m_control this) & CONTROL_SPSEL)
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

                        (if (ß (:m_imm this) == 0)
                            (do
                                ;; Enable
                                (ß (:m_primask this) &= ~PRIMASK_PM)
                            )
                            (do
                                ;; Disable
                                (ß (:m_primask this) |= PRIMASK_PM)
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
            (if (ß (:m_rd this) == reg'SP)
                (ß armv6m_update_sp(this, reg_rd))
                (ß (:m_regfile this)[(:m_rd this)] = reg_rd)
            )
        )

        ;; Can't perform a writeback to PC using normal mechanism as this is a special register...
        (when (ß write_rd)
            (ß assert((:m_rd this) != reg'PC))
        )

        (ß (:m_regfile this)[reg'PC] = pc)
        nil
    )
)
