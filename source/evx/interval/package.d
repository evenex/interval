module evx.interval;

private {//import
	import std.algorithm: min, max;

	import evx.meta;
	import evx.infinity;
}

/**
	 predicate to test for intervals
*/
enum is_interval (T) = is (T == Interval!U, U...);

/**
	 half-open interval type, suitable for bounds checking
*/
struct Interval (LeftType, RightType)
if (All!(Not!(λ!q{(T) = is (T == const(T))}), LeftType, RightType))
{
	alias Left = LeftType; alias Right = RightType;
	static assert (is (Finite!Left == Finite!Right));

	auto left = -Left ();
	auto right = Right ();

	alias Element = Finite!Left;

	mixin IntervalBase;
}
/**
    ditto
*/
template Interval (Left, Right)
if (Any!(λ!q{(T) = is (T == const(T))}, Left, Right))
{
	alias Interval = Interval!(Unqual!Left, Unqual!Right);
}
/**
    ditto
*/
alias Interval (T) = Interval!(T,T);
///
unittest {
	Interval!int x0;
	Interval!uint x1;
	Interval!(uint, Infinite!uint) x2;
	static assert (not (is (Interval!(Infinite!int, Infinite!uint))));
	Interval!(Infinite!int, Infinite!int) x3;

	enum inf = real.infinity;

	assert (x0 == [0, 0]);
	assert (x1 == [0, 0]);
	assert (x2 == [0, inf]);
	assert (x3 == [-inf, inf]);

	auto y0 = interval (1,2);
	auto y1 = interval (1, infinity);
	auto y2 = interval (-infinity, infinity);
	auto y3 = interval!int (-infinity, infinity);
	auto y4 = interval!real (-infinity, infinity);

	assert (y0 == [1, 2]);
	assert (y1 == [1, inf]);
	assert (y2 == [-inf, inf]);
	assert (y3 == [-inf, inf]);
	assert (y4 == [-inf, inf]);
}

/**
	
	untyped infinite interval
*/
struct Interval (T : void)
{
	alias Element = void;

	static left ()
	{
		return -infinity;
	}
	static right ()
	{
		return infinity;
	}

	mixin IntervalBase;
}

auto fmap (alias f, Left, Right)(Interval!(Left, Right) bounds)
{
	return interval (f(bounds.left), f(bounds.right));
}

/**
	 interval constructors 
*/
auto interval (T)(Infinite!void left, Infinite!void right)
in {
	assert (left.is_negative && right.is_positive);
}
body {
	return Interval!(Repeat!(2, Infinite!T))();
}
/**
    ditto
*/
auto interval (Infinite!void left, Infinite!void right)
in {
	assert (left.is_negative && right.is_positive);
}
body {
	return Interval!void ();
}
/**
    ditto
*/
auto interval (T)(T[2] bounds)
{
	return Interval!T (bounds[0], bounds[1]);
}
/**
    ditto
*/
auto interval (T,U)(T left, U right)
{
	static if (is (T == Infinite!V, V))
	{}
	static if (is (U == Infinite!W, W))
	{}

	static if (is (V == void) && is (W == void))
		static assert (0, `infinite interval declared without type`);

	else static if (is (V == void))
		return Interval!(Infinite!U, U)(-infinity!U, right);

	else static if (is (W == void))
		return Interval!(T, Infinite!T)(left, infinity!T);

	else static if (is (V) && is (W))
		return Interval!(T,U)(left, right);

	else static if (is (V))
		return Interval!(T, CommonType!(V,U))(left, right);

	else static if (is (W))
		return Interval!(CommonType!(T,W), U)(left, right);

	else return Interval!(CommonType!(T,U))(left, right);
}
/**
    ditto
*/
auto interval (T)(T point)
if (not (is (T == U[2], U) || is (T == Infinite!U, U)))
{
	static if (is (T == Interval!U, U...))
		return point;
	else return interval (point, point);
}
///
unittest {
	auto a = interval (0, 10);
	assert (a.width == 10);

	a.left = 9;
	assert (a.width == 1);

	a.right = 9;
	assert (a.width == 0);

	auto b = [-10, 5].interval;
	assert (b.width == 15);

	auto c = interval (6);
	assert (c.left == 6);
	assert (c.right == 6);
	assert (c.width == 0);

	auto d = interval (c);
	assert (d.left == 6);
	assert (d.right == 6);
	assert (d.width == 0);

	auto e = interval (-infinity!real, infinity!real);
	assert (e.left == -infinity);
	assert (e.right == real.infinity);
	assert (e.width == infinity);
}

/**
	 distance between the endpoints of an interval
*/
auto width (T)(T interval)
if (is_interval!T)
{
	return interval.right - interval.left;
}
///
unittest {
    assert (interval (0,10).width == 10);
    assert (interval (2.5, 5.0).width == 2.5);
}

/**
	 test if two intervals overlap 
*/
bool overlaps (T,U)(T a, U b)
if (All!(is_interval, T, U))
{
	if (a.left < b.left)
		return b.left < a.right;
	else return a.left < b.right;
}
///
unittest {
	auto a = interval (0, 10);
	auto b = interval (11, 13);

	assert (a.left < b.left);
	assert (a.right < b.left);

	assert (a.not!overlaps (b));
	a.right = 11;
	assert (a.not!overlaps (b));
	a.right = 12;
	assert (a.overlaps (b));
	b.left = 13;
	assert (a.not!overlaps (b));
}

/**
	 test if an interval is contained within another 
*/
bool is_contained_in (T,U)(T a, U b)
if (All!(is_interval, T, U))
{
	return a.left >= b.left && a.right <= b.right;
}
///
unittest {
	auto a = interval (0, 10);
	auto b = interval (1, 5);
	auto c = interval (10, 11);
	auto d = interval (9, 17);
	auto e = interval (-infinity, infinity);

	assert (a.not!is_contained_in (b));
	assert (a.not!is_contained_in (c));
	assert (a.not!is_contained_in (d));

	assert (b.is_contained_in (a));
	assert (b.not!is_contained_in (c));
	assert (b.not!is_contained_in (d));

	assert (c.not!is_contained_in (a));
	assert (c.not!is_contained_in (b));
	assert (c.is_contained_in (d));

	assert (d.not!is_contained_in (a));
	assert (d.not!is_contained_in (b));
	assert (d.not!is_contained_in (c));

	assert (a.is_contained_in (e));
	assert (b.is_contained_in (e));
	assert (c.is_contained_in (e));
	assert (d.is_contained_in (e));

	assert (e.not!is_contained_in (a));
	assert (e.not!is_contained_in (b));
	assert (e.not!is_contained_in (c));
	assert (e.not!is_contained_in (d));
}

/**
	 test if a point is contained within an interval 
*/
bool is_contained_in (T,U)(T point, U interval)
if (not (is_interval!T) && is_interval!U)
{
	static if (is (T == V[2], V)) // REVIEW
	{
		auto x = point[0];
		auto y = point[1];

		bool y_check = (interval.left <= y && y < interval.right)
			|| (interval.left == interval.right && y == interval.left);
	}
	else {
		alias x = point;
		bool y_check = true;
	}

	return y_check && (
		(interval.left <= x && x < interval.right)
		|| (interval.left == interval.right && x == interval.left)
	);
}
///
unittest {
    assert (1.is_contained_in (interval (0,2)));
    assert (6.not!is_contained_in (interval (0,2)));
}

/**
	 test if a point is between two values, inclusive 
*/
bool between (T, U, V) (T t, U t0, V t1) 
{
	return t0 <= t && t <= t1;
}
///
unittest {
    assert (1.between (0,2));
    assert (6.not!between (0,2));
}

/**
	 clamp a value to an interval 
*/
auto clamp (T,U)(T value, U interval)
if (is_interval!U)
{
	value = max (value, interval.left);
	value = min (value, interval.right);

	return value;
}
///
unittest {
    assert (5.clamp (interval (0, 3)) == 3);
    assert ((-10).clamp (interval (0, 3)) == 0);
}

/**
	
	measure the limit of ranges
*/
Interval!size_t limit (uint i : 0, S)(const S space)
{
	return interval!size_t (0, space.length);
}
///
unittest {
    assert ([1,2,3,4].limit!0 == interval (0,4));
}

private {//impl
	template IntervalBase ()
	{
		auto opEquals (T...)(const Interval!T that) const
		{
			return this.left == that.left
				&& this.right == that.right;
		}
		auto opEquals (T)(const T[2] that) const
		{
			return this.left == that[0]
				&& this.right == that[1];
		}

		auto opBinary (string op, T)(T that)
		if (not (is_interval!T))
		out {assertion;}
		body {
			return mixin(q{
				this } ~op~ q{ that.interval
			});
		}
		auto opBinary (string op, T...)(Interval!T that)
		out {assertion;}
		body {
			return mixin(q{
				interval (
					this.left } ~op~ q{ that.left,
					this.right } ~op~ q{ that.right,
				)
			});
		}
		auto ref opOpAssign (string op)(Element point)
		out {assertion;}
		body {
			mixin(q{
				left } ~op~ q{= point;
				right } ~op~ q{= point;
			});

			return this;
		}
		auto ref opOpAssign (string op, T...)(Interval!T interval)
		out {assertion;}
		body {
			mixin(q{
				left } ~op~ q{= interval.left;
				right } ~op~ q{= interval.right;
			});
		}

		auto ref opAssign (T...)(Interval!T interval)
		out {assertion;}
		body {
			this.left = interval.left;
			this.right = interval.right;

			return this;
		}
		auto ref opAssign ()(Element point)
		out {assertion;}
		body {
			this.left = this.right = point;

			return this;
		}

		private void assertion () 
		{
			assert (left <= right, this.text ~ ` is out of order`);
		}
	}
}
