.data

arr:	.word	4,3,2,1,5
arl:	.word	5

.text
	la	$s0 arr
	li	$a0 0
	li	$t3 0
	lw	$t2 arl
ini:	bge	$a0 $t2 end
	lw	$t0 ($s0)
	add	$t3 $t3 $t0
	addi	$s0 $s0 4
	addi	$a0 $a0 1
	j	ini
end: