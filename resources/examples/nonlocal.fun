def f(): i64 {
	label b {
		g(1, b) + 2
	}
}

def g(x: i64, c: cns i64): i64 {
	if x == 0 {
		goto c (0)
	} else {
		x + x
	}
}
