data Unit { U }
codata Fun { ap(x: Unit): Unit }

def f(): Unit {
	let u: Unit = U;
	let h: Fun = new { ap(x) => U };
	h.ap(g().ap(u))
}

def g(): Fun { new { ap(x) => U } }
