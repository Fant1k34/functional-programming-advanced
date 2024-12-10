method is_even(n : nat) returns (result: bool)
    ensures result == (n % 2 == 0)
{
    result := n % 2 == 0;

    return result;
}

method sum_from_to(start : nat, end : nat) returns (result : nat)
    requires start <= end
    decreases end - start
{
    if (start == end) {
        result := start;
    } else {
        var prev_value := sum_from_to(start, end - 1);

        result := prev_value + end;
    }
}

function method factorial(n : int): int 
    decreases n
{
    if ( n <= 1) then n else factorial(n - 1) + factorial(n - 2)
}

method reverse_seq(list: array<int>) returns (result: array<int>) 
    ensures list.Length == result.Length
{
    var i := 0;
    var reversed_list := new int[list.Length] (_ => 0);

    while (i < list.Length)
    invariant 0 <= i <= list.Length
    invariant -1 <= list.Length - 1 - i < reversed_list.Length
    invariant list.Length == reversed_list.Length
    {
        reversed_list[list.Length - 1 - i] := list[i];
        i := i + 1;
    }

    result := reversed_list;
}



method Main() {
    print("Hello, world!" + "\n");

    // running Main with F5 (doesn't really differ)
    var arr := new int[3] (_ => 0);
    arr[0] := 4;
    arr[1] := 3;
    arr[2] := -9;

    var a := reverse_seq(arr); 

    print(a[0], "\n");
}
