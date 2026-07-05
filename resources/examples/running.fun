data List { Nil, Cons(x: i64, xs: List) }
data Bool { True, False }
codata Pred { apply(x: i64): Bool }

def all(p: Pred, l: List): Bool {
	l.case {
		Nil => True,
		Cons(x, xs) => p.apply(x).case {
			True => all(p, xs),
			False => False,
		}
	}
}

def foo(): Bool {
	let l: List = Cons(0, Cons(1, Nil));
	let p: Pred = new { apply(x) => if x == 0 { True } else { False } };
	all(p, l)
}
