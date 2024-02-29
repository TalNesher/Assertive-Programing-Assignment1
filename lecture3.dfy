/*

Assertive Programming - Fall Semester 2024 - Lecture #3 (17/1/24)

Last week:

- a first look at proof obligations / verification conditions
- a second implementation of the natural square-root specification

Today:

- (ghost) functions vs. (compilable, executable) methods
- recursive definition (in the spec) vs. iterative code (in the implementation)
- more on how to document proof obligations
- develop a method to compute the n-th Fibonacci number, iteratively
- preconditions

*/

ghost function Fib(n: int): int
    requires n >= 0
{
    if n == 0 then
        0
    else if n == 1 then
        1
    else
        assert n >= 2; // not necessary, just documenting, to be sure of the precondition
        Fib(n-2) + Fib(n-1)
}

method {:verify true} ComputeFib'(n: int) returns (b: int)
    requires n >= 0
    ensures b == Fib(n)
{
    if n == 0 {
        return 0; 
    }
    var i, a;
    i, a, b := 1, 0, 1;
    while i < n
        invariant 1 <= i <= n
        invariant a == Fib(i-1) && b == Fib(i)
    {
        a, b := b, a + b;
        i := i+1;
    }
}

method {:verify true} ComputeFib(n: int) returns (b: int)
    requires n >= 0
    ensures b == Fib(n)
{
    assert n >= 0;
    if n == 0 {
        assert n == 0;
        // ==>
        assert 0 == Fib(n); // by the definition of Fib
        return 0; 
    }
    else {
        assert n >= 0;
        assert n != 0;
        // ==>?
        assert 1 <= 1 <= n && 0 == Fib(1-1) && 1 == Fib(1);
    }
    // n := n-1; // LHS of assignment must denote a mutable variable
    var i, a;
    assert 1 <= 1 <= n && 0 == Fib(1-1) && 1 == Fib(1);
    i, a, b := 1, 0, 1;
    assert 1 <= i <= n && a == Fib(i-1) && b == Fib(i);
    while i < n
        invariant 1 <= i <= n
        invariant a == Fib(i-1) && b == Fib(i)
        decreases n-i // added after the lecture: Dafny was convinced of termination by itself, in the future we'd wish to document this too
    {
        assert 1 <= i <= n && a == Fib(i-1) && b == Fib(i); // from the loop invariant
        assert i < n; // from the loop guard
        assert Fib(i+1) == Fib(i-1) + Fib(i);
        // ==>?
        assert 1 <= i+1 <= n && b == Fib(i) && a + b == Fib(i+1);
        a, b := b, a + b;
        assert 1 <= i+1 <= n && a == Fib(i+1-1) && b == Fib(i+1);
        i := i+1;
        assert 1 <= i <= n && a == Fib(i-1) && b == Fib(i);
    }
    assert 1 <= i <= n && a == Fib(i-1) && b == Fib(i); // from the loop invariant
    assert i >= n; // negation of the loop guard
    // ==>
    assert b == Fib(n);
}

method {:verify true} Main() {
	// 0 1 1 2 3 5 8 13 21 34 55 ...
	var x :=  ComputeFib(7);
    assert x == 13;
	print "The Fibonacci number of 7 is ", x, "\n";

	x :=  ComputeFib(1000000);
    assert x == Fib(1000000);
	print "The Fibonacci number of 1000000 is ", x, "\n";

    // a call to a ghost function is allowed only in specification contexts (consider declaring the function without the 'ghost' keyword)
	// print "The Fibonacci number of 7 is ", Fib(7), "\n";

    // a precondition for this call could not be proved Verifier
    // lecture03.dfy(33, 14): this is the precondition that could not be proved
	// x := ComputeFib(-7);
}