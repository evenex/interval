module evx.interval.infinity;

private {/*import}*/
	import std.conv: text;
	import std.traits: isIntegral, isUnsigned, Select, CommonType;

	import evx.meta;
}

/* test the sign of a value
*/
bool is_negative (T)(T x)
	{/*...}*/
		return x < T(0);
	}
bool is_positive (T)(T x)
	{/*...}*/
		return x > T(0);
	}

/* convenience constructor for infinite numbers 
*/
template infinity (T)
	if (is (typeof(T(real.init))))
	{/*...}*/
		enum infinity = T(real.infinity);
	}
template infinity (T)
	if (isIntegral!T)
	{/*...}*/
		enum infinity = Infinite!T ();
	}
template infinity (T)
	if (is (T == Infinite!U, U))
	{/*...}*/
		enum infinity = T ();
	}

/* type-agnostic infinity constructor
*/
auto infinity ()()
	{/*...}*/
		return Infinite!void ();
	}

/* test if a value represents +/- infinity
*/
bool is_infinite (T)(T x)
	{/*...}*/
		return x == real.infinity || x == -real.infinity;
	}

/* wrapper for integral or type-agonistic infinity 
*/
struct Infinite (T)
	if (isIntegral!T || is (T == void))
	{/*...}*/
		static if (isUnsigned!T)
			enum is_negative = false;
		else bool is_negative;

		auto is_positive () const {return not (is_negative);}

		enum is_infinite = true;

		auto opUnary (string op)() const
			{/*...}*/
				static if (op == `+`)
					return this;
				else static if (op == `-`)
					{/*...}*/
						static if (isUnsigned!T)
							static assert (0, `cannot construct ` ~op ~ Infinite.stringof);
						else return Infinite (true);
					}
			}
		auto opBinary (string op, U)(U that) const
			{/*...}*/
				static if (is (U == Infinite!V, V))
					{}

				static if (op == `+` || op == `-`)
					{/*...}*/
						static if (is (V))
							{/*...}*/
								static if (op == `+`)
									auto sign_mismatch = that.is_positive != this.is_positive;
								else auto sign_mismatch = that.is_positive == this.is_positive;

								if (sign_mismatch)
									assert (0, this.toString ~ op ~ that.toString~ ` undefined`);
								else return this;
							}
						else return this;
					}
				else static if (op == `*`)
					{/*...}*/
						if (that == U(0) && not (is (V)))
							assert (0, this.toString ~ op ~ that.text~ ` undefined`);
						else return Infinite (that.is_negative != this.is_negative);
					}
				else static if (op == `/`)
					{/*...}*/
						if (is (V))
							assert (0, this.toString ~ op ~ that.text~ ` undefined`);
						else if (this.is_positive != that.is_positive)
							return Infinite (true);
						else return this;
					}
				else static if (op == `^^`)
					{/*...}*/
						return (this.is_negative? -real.infinity : real.infinity) ^^ that;
					}
				else static assert (0, op~ ` is not implemented for ` ~Infinite.stringof);
			}
		auto opBinaryRight (string op, U)(U that) const
			{/*...}*/
				static if (op == `+`)
					return this;
				else static if (op == `-`)
					return -this;
				else static if (op == `*`)
					return this * that;
				else static if (op == `/`)
					return U(0);
				else static if (op == `^^`)
					return that ^^ (this.is_negative? -real.infinity : real.infinity);
				else static assert (0, op~ ` is not implemented for ` ~Infinite.stringof);
			}

		auto opCmp (U)(auto ref U that) const
			{/*...}*/
				if (this == that)
					return 0;
				else return this.is_positive? 1 : -1;
			}
		auto opEquals (U)(auto ref U that) const
			{/*...}*/
				return that.is_infinite 
					&& this.is_negative == that.is_negative;
			}

		auto opCast (U)() const
			if (is (U == Infinite!V, V))
			{/*...}*/
				auto inf = U ();

				static if (is (typeof((){enum _ = U.is_negative;})))
					return inf;
				else return is_positive? inf : -inf;
			}

		auto toString () const
			{/*...}*/
				if (is_negative)
					return `-inf`;
				else return `inf`;
			}
	}

/* floating-point overload aliases itself to floating-point infinity 
*/
struct Infinite (T)
	if (is (typeof(T(real.init))))
	{/*...}*/
		enum is_negative = false;
		enum is_positive = true;

		enum value = T(real.infinity);
		alias value this;
	}

/*
	identity alias 
*/
template Infinite (T)
	if (is (T == Infinite!U, U))
	{/*...}*/
		alias Infinite = T;
	}

/*
	inverse alias 
*/
alias Finite (T) = Select!(
	is (T == Infinite!U, U),
	Unwrapped!T, T
);

unittest {/*...}*/
	Infinite!int i;
	Infinite!uint u;
	Infinite!real x;

	static assert (not (is (typeof(-u))));

	assert (u == i);
	assert (u == x);
	assert (i == x);
	assert (i != -i);
	assert (x != -x);

	/*				-i				i					-x					x 			*/
	/* -i */ assert (-i == -i);	assert (-i < i);	assert (-i == -x); 	assert (-i < x);
	/*  i */ assert (i > -i);	assert (i == i);	assert (i > -x);	assert (i == x);
	/* -x */ assert (-x == -i);	assert (-x < i);	assert (i > -x);	assert (i == x);
	/*  x */ assert (x > -i);	assert (x == i);	assert (x > -x);	assert (x == x);

	assert (real.max < x);
	assert (real.max < i);
	assert (-real.max > -x);
	assert (-real.max > -i);

	assert (x + 1 == x);
	assert (x - 1 == x);
	assert (i + 1 == i);
	assert (i - 1 == i);
	assert (1 + x == x);
	assert (1 - x == -x);
	assert (1 + i == i);
	assert (1 - i == -i);
}
unittest {/*...}*/
	void test_infinity (T)(T inf)
		{/*...}*/
			void assertNaN (T)(lazy T val)
				{/*...}*/
					import std.math;
					import std.exception: assertThrown;

					static if (is (T == Infinite!U, U))
						assertThrown!Error (val);
					else assert (std.math.isNaN (val));
				}

			assert (inf + 4 == inf);
			assert (inf - 3  == inf);

			assert (inf * 4  == inf);
			assert (inf * (-2)  == -inf);
			assertNaN (inf * 0);

			assert (inf ^^ (0)  == 1);
			assert (inf ^^ (2)  == inf);
			assert (inf ^^ (-2)  == 0);

			assert (2 ^^ (inf)  == inf);
			assert (-2 ^^ (inf)  == -inf);
			assert (2 ^^ (-inf)  == 0);
			assert (-2 ^^ (-inf)  == 0);

			assert (2 / (inf)  == 0);
			assert (-2 / (inf)  == 0);
			assert ((inf)/2  == inf);
			assert ((inf)/(-2)  == -inf);

			assert ((inf)+(inf)  == inf);
			assertNaN (inf - inf);

			assert ((inf)*(inf)  == inf);
			assert ((inf)*(-inf)  == -inf);

			assertNaN (inf / inf);
			assertNaN (inf /(-inf));

			assert ((inf)^^(inf)  == inf);
			assert ((-inf)^^(inf)  == inf);
			assert ((inf)^^(-inf)  == 0);
			assert ((-inf)^^(-inf)  == 0);

			assert (inf + inf == inf);
			assert (inf - 10 == inf);
			assert (-inf + 10 == -inf);
		}

	auto r_inf = real.infinity;
	auto i_inf = Infinite!int ();
	auto v_inf = Infinite!void ();

	test_infinity (r_inf);
	test_infinity (i_inf);
	test_infinity (v_inf);
}
