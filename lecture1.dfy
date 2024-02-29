/*

Assertive Programming - Fall Semester 2024 - Lecture #1 (3/1/24)

Lectures: Wednesdays 18-20 in classroom 208 building 32
Lecturer: R. Ettinger, ranger@cs.bgu.ac.il, room -104 building 58 (Mathematics), office hours: Wednesdays from 20:10 (after the lecture)

Today: about the course + a first little program

Dafny.org, Ada/SPARK

*/

method {:verify true} Sqrt(n: nat) returns (a: nat)
	ensures a*a <= n < (a+1)*(a+1)
{
	a := 0;
	while !(n < (a+1)*(a+1))
		invariant a*a <= n
		decreases n - a*a
	{
		a := a+1;
	}
	assert n < (a+1)*(a+1); // negation of the loop guard
	assert a*a <= n; // from the loop invariant
	// ==>
	assert a*a <= n < (a+1)*(a+1); // the postcondition
	// a return statement is not necessary:
	// the value of "a" will be returned anyway (as it is listed in the method's signature)
	// return a;
}

method Main()
{
	var a := Sqrt(10);
	assert a == 3;
	print "The floor of the square root of 10 is ";
	print a;

	a := Sqrt(9);
	assert a == 3;
	print "\nThe floor of the square root of 9 is ";
	print a;

	a := Sqrt(8);
	assert a == 2;
	print "\nThe floor of the square root of 8 is ";
	print a;

	a := Sqrt(1);
	assert a == 1;
	print "\nThe floor of the square root of 1 is ";
	print a;

	a := Sqrt(0);
	assert a == 0;
	print "\nThe floor of the square root of 0 is ";
	print a;
}