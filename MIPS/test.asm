.data

exp_long(int, int):
        addiu   $sp,$sp,-24
        sw      $fp,20($sp)
        move    $fp,$sp
        sw      $4,24($fp)
        sw      $5,28($fp)
        li      $2,1                        # 0x1
        sw      $2,8($fp)
        lw      $2,24($fp)
        nop
        sw      $2,12($fp)
$L5:
        lw      $2,28($fp)
        nop
        slt     $2,$2,2
        bne     $2,$0,$L2
        nop

        lw      $3,28($fp)
        li      $2,-2147483648                  # 0xffffffff80000000
        ori     $2,$2,0x1
        and     $2,$3,$2
        bgez    $2,$L3
        nop

        addiu   $2,$2,-1
        li      $3,-2                 # 0xfffffffffffffffe
        or      $2,$2,$3
        addiu   $2,$2,1
$L3:
        move    $3,$2
        li      $2,1                        # 0x1
        bne     $3,$2,$L4
        nop

        lw      $3,8($fp)
        lw      $2,12($fp)
        nop
        mult    $3,$2
        mflo    $2
        sw      $2,8($fp)
$L4:
        lw      $2,28($fp)
        nop
        srl     $3,$2,31
        addu    $2,$3,$2
        sra     $2,$2,1
        sw      $2,28($fp)
        lw      $3,12($fp)
        lw      $2,12($fp)
        nop
        mult    $3,$2
        mflo    $2
        sw      $2,12($fp)
        b       $L5
        nop

$L2:
        lw      $3,8($fp)
        lw      $2,12($fp)
        nop
        mult    $3,$2
        mflo    $2
        sw      $2,8($fp)
        lw      $2,8($fp)
        move    $sp,$fp
        lw      $fp,20($sp)
        addiu   $sp,$sp,24
        j       $31
        nop