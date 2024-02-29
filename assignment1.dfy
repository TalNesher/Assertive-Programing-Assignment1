/*
	Part A (15%)

	Goal:

	Complete the definition of the program entities below:
	"Guard1", "Inv1", "V1", "Init1", "LoopBody1" and "Lemma1",
	by providing a body, such that the methods ("Init1" and "LoopBody1")
	and the lemma ("Lemma1") will be verifiably correct.

	No need to document the proof obligations.

*/
predicate Guard1(n: int, a: int)
	requires Inv1(n, a)
	{
		!(a * a <= n)
	}
	

predicate Inv1(n: int, a: int){
	
	(a+1) * (a+1) > n && n >= 0 && a >= 0

}

function V1(a: int): int
{
	a
}

method Init1(n: int) returns (a: int)
	requires n >= 0
	ensures Inv1(n, a) 
	{
		a := n;
	}

method {:verify true} LoopBody1(n: int, a0: int) returns (a: int)
	requires Inv1(n, a0) && Guard1(n, a0)
	ensures Inv1(n, a) && 0 <= V1(a) < V1(a0)
	{
		
		a := a0 - 1;

	}

lemma Lemma1(n: int, a: int)
	requires Inv1(n, a) && !Guard1(n, a)
	ensures a*a <= n && n < (a+1)*(a+1)
	{}

method Sqrt_Down_Loop(n: int) returns (a: int)
	requires n >= 0
	ensures a*a <= n && n < (a+1)*(a+1)
{
	a := Init1(n);
	while Guard1(n, a)
		invariant Inv1(n, a)
		decreases V1(a)
	{
		a := LoopBody1(n, a);
	}
	Lemma1(n, a);
}

/*
	Part B (15%)

	Goal:

	Complete the definition of the program entities below:
	"Guard2", "Inv2", "V2", "Init2", "LoopBody2" and "Lemma2",
	by providing a body, such that the methods ("Init2" and "LoopBody2")
	and the lemma ("Lemma2") will be verifiably correct.

	No need to document the proof obligations.

	Restriction:

	Each of the two methods should be implemented with one assignment statement.

*/

function Fib(n: nat): nat
	decreases n
{
	if n == 0 then 0 else if n == 1 then 1 else Fib(n-2) + Fib(n-1)
}

predicate Guard2(n: nat, i: nat, a: nat, b: nat)
	requires Inv2(n, i, a, b)
	{
		i < n
	}

predicate Inv2(n: nat, i: nat, a: nat, b: nat)
{
	0 <= i <= n && a == Fib(i) && b == Fib(i+1)
}

function V2(n: nat, i: nat, a: nat, b: nat): int
{
	n - i
}

method Init2(n: nat) returns (i: nat, a: nat, b: nat)
	ensures Inv2(n, i, a, b)
	{
		i, a, b := 0, 0, 1;
	}

method LoopBody2(n: nat, i0: nat, a0: nat, b0: nat) returns (i: nat, a: nat, b: nat)
	requires Inv2(n, i0, a0, b0) && Guard2(n, i0, a0, b0)
	ensures Inv2(n, i, a, b) && 0 <= V2(n, i, a, b) < V2(n, i0, a0, b0)
	{
		a, b, i := b0, a0 + b0, i0 + 1;
	}

lemma Lemma2(n: nat, i: nat, a: nat, b: nat)
	requires Inv2(n, i, a, b) && !Guard2(n, i, a, b)
	ensures a == Fib(n)
	{}

method ComputeFib2(n: nat) returns (a: nat)
	ensures a == Fib(n)
{
	var i: nat, b: nat;
	i, a, b := Init2(n);
	while Guard2(n, i, a, b)
		invariant Inv2(n, i, a, b)
		decreases V2(n, i, a, b)
	{
		i, a, b := LoopBody2(n, i, a, b);
	}
	Lemma2(n, i, a, b);
}

predicate ValidTimeOfDay(h: int, m: int) { 0 <= h < 24 && 0 <= m < 60 }

//-------------------------
/*
	Part C (30%)

	Goal:

	Implement correctly, using a "while" loop, **documenting the proof obligations**
	as we've learned, with assertions and a lemma for each proof goal.

	No need to document the proof obligations.

	Restriction:

	The only arithmetic operations allowed in your *code* are increment and decrement,
	using "x := plus_one(x);" and "x := minus_one(x);" for any variable "x", whereas
	other operations (such as addition, subtraction, multiplication, division, or modulo)
	may be used in *specification contexts* only (such as assertions and loop invariants).
*/
method {:verify true} TimeOfDay(minutes_since_midnight: int) returns (h: int, m: int)
	requires 0 <= minutes_since_midnight < 24*60
	ensures h*60+m == minutes_since_midnight
	ensures ValidTimeOfDay(h, m)
	{
		h := 0;
		m := minutes_since_midnight;
		while m >= 60
			invariant h*60+m == minutes_since_midnight
			decreases m
		{
			h := plus_one(h);
			var i := 0;
			var old_m := m;
    		while i < 60
        		invariant 0 <= i <= 60
				invariant m == old_m - i
        		decreases 60 - i
    		{
				m ,i := minus_one(m), plus_one(i);
    		}
			assert m == old_m - 60;
		}
		assert ValidTimeOfDay(h, m);
	}



function plus_one(x: int): int { x+1 }
function minus_one(x: int): int { x-1 }

/*
	Part D (40%)

	Goal: Implement correctly, using a "while" loop, **documenting the proof obligations**
	as we've learned, with assertions and a lemma for each proof goal.

	Restriction:

	In contrast to Part C above, the only arithmetic operation allowed in your *code*
	this time is addition, using "x := add(y, z);" for any variable "x" and variables or
	integer constants y and z, whereas other operations (such as multiplication, division, or modulo)
	may be used in *specification contexts* only (such as assertions and loop invariants).

*/



lemma ProofPostLoop(d: int, h: int, m: int, start_h: int, start_m: int, minutes: int)
	requires h < 24
	requires inv(d, h, m, start_h, start_m, minutes) && m < 60
	ensures ValidTimeOfDay(h, m)
	ensures start_h*60 + start_m + minutes == d*24*60 + h*60 + m
	{}

lemma ProofInit(start_h: int, start_m: int, minutes: int)
	requires ValidTimeOfDay(start_h, start_m)
	ensures inv(0, start_h, minutes + start_m, start_h, start_m, minutes)
	{}

lemma ProofLoopBody(d: int, h: int, m: int, start_h: int, start_m: int, minutes: int, V0: int)
	requires V0 == m
	requires m >= 60
	requires h < 24
	requires inv(d, h, m, start_h, start_m, minutes)
	ensures inv(d, h + 1, m - 60, start_h, start_m, minutes)
	ensures 0 <= m - 60 < V0
	{}

lemma ifLoopBody(d: int, h: int, m: int, start_h: int, start_m: int, minutes: int, V0: int) 
	requires h == 24
	requires  inv(d, h, m - 60, start_h, start_m, minutes)
	requires 0 <= m - 60 < V0
	ensures inv(d + 1, 0, m - 60, start_h, start_m, minutes)
	ensures 0 <= m - 60 < V0
	{}


lemma elseLoopBody(d: int, h: int, m: int, start_h: int, start_m: int, minutes: int, V0: int) 
	requires inv(d, h, m - 60, start_h, start_m, minutes)
	requires 0 <= m - 60 < V0
	ensures inv(d, h, m - 60, start_h, start_m, minutes)
	ensures 0 <= m - 60 < V0
{}

predicate inv(d: int, h: int, m: int, start_h: int, start_m: int, minutes: int){
	0 <= m && start_h*60 + start_m + minutes == d*24*60 + h*60 + m && 0 <= h <= 24
}


method {:verify true} UpdateTime(start_h: int, start_m: int, minutes: int) returns (d: int, h: int, m: int)
	requires ValidTimeOfDay(start_h, start_m)
	ensures ValidTimeOfDay(h, m)
	ensures start_h*60 + start_m + minutes == d*24*60 + h*60 + m
	{	
		ProofInit(start_h, start_m, minutes);
		assert inv(0, start_h, minutes + start_m, start_h, start_m, minutes);
		d := 0;
		h := start_h;
		m := add(minutes, start_m);
		assert h < 24;//////////////////////////////////////
		assert inv(d, h, m, start_h, start_m, minutes);
		while(60 <= m)
			decreases m
			invariant inv(d, h, m, start_h, start_m, minutes)
		{
			ghost var V0 := m;
			assert V0 == m;
			assert 60 <= m;
			assert inv(d, h, m, start_h, start_m, minutes);
			ProofLoopBody(d, h, m, start_h, start_m, minutes, V0);
			assert inv(d, h + 1, m - 60, start_h, start_m, minutes);
			assert 0 <= m - 60 < V0;
			h := add(h, 1);
			assert inv(d, h, m - 60, start_h, start_m, minutes);
			assert 0 <= m - 60 < V0;
			if h == 24 {
				assert h == 24;
				ifLoopBody(d, h, m, start_h, start_m, minutes, V0);
				assert inv(d + 1, 0, m - 60, start_h, start_m, minutes);
				assert 0 <= m - 60 < V0;
				h := 0;
				assert inv(d + 1, h, m - 60, start_h, start_m, minutes);
				assert 0 <= m - 60 < V0;
				d := add(d, 1);
				assert inv(d, h, m - 60, start_h, start_m, minutes);
				assert 0 <= m - 60 < V0;
			}
			else {
				elseLoopBody(d, h, m, start_h, start_m, minutes, V0);
				assert inv(d, h, m - 60, start_h, start_m, minutes);
				assert 0 <= m - 60 < V0;
			}
			assert inv(d, h, m - 60, start_h, start_m, minutes);
			assert 0 <= m - 60 < V0;
			m := add(m, -60);
			assert inv(d, h, m, start_h, start_m, minutes);
			assert 0 <= m < V0;
			assert h < 24;//////////////////////////////////////
		}
		assert h < 24;
		assert inv(d, h, m, start_h, start_m, minutes) && m < 60;
		ProofPostLoop(d, h, m, start_h, start_m, minutes);
		assert ValidTimeOfDay(h, m);
		assert start_h*60 + start_m + minutes == d*24*60 + h*60 + m;
	}

function add(y: int, z: int): int { y+z }


method {:verify true} Main() {
	var d, h, m := UpdateTime(23, 30, 2340);
	print "\nd: ", d, "\nh: ", h, "\nm: ", m;

	// var minuts_passed := 250;
	// var hour, minut := TimeOfDay(minuts_passed);
	// print "Time is: ", hour, ":", minut;
}