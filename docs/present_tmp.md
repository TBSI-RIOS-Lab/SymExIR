# TMP PRESENT

## Simple Case 1

The example in the following code block contains a simple set of integer-related instruction operations. The code snippet above is used for verification, and the values below are the ones being verified.

```
test_case_int = [
    "%1 = load i32, i32* %5, align 8, !tbaa !4",
    "%6 = load i32, i32* %5, align 8, !tbaa !4",
    "%7 = add i32 %6, %1",
    "%9 = load i32, i32* %8, align 8, !tbaa !4",
    "%10 = add i32 %9, %1",
    "%11 = mul i32 %10, %1",
    "%12 = udiv i32 %10, %1",
    "%13 = sub i32 %10, %1",
    "%14 = add i32 %10, %1",
    "%15 = urem i32 %10, %1",
    "%16 = icmp ne i32 %14, %15",
    "%17 = and i32 %12, %14",
    "%18 = or i32 %12, %14",
    "%19 = xor i32 4, %14",
    "%20 = xor i64 4, 1",
    "%21 = xor i32 4, 1",
    "%22 = xor i1 0, 1",
]

test_case_int_info = [
    (0, "1"),
    (1, "1"),
    (2, "2"),
    (3, "300"),
    (4, "301"),
    (5, "301"),
    (6, "301"),
    (7, "300"),
    (8, "302"),
    (9, "0"),
    (10, "0"),
    (11, "300"),
    (12, "303"),
    (13, "298"),
    (14, "5"),
    (15, "5"),
    (16, "1"),
]
```
