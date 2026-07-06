data Unit { U }
codata Fun { apply(u: Unit): Unit }

def f(): Unit {
	let x: Unit = U;
	let h: Fun = new { apply(u) => U };
	h.apply(g().apply(x))
}

def g(): Fun { new { apply(u) => u } }
