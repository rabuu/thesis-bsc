def f(): i64 {
	g(1) + 2
}

def g(x: i64): i64 {
	x + x
}

def g2(x: i64): i64 {
	if x == 0 {
		42
	} else {
		x + x
	}
}
