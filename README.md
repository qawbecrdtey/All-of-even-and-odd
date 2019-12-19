# All of even and odd

The `All_of_even_and_odd.v` file contains many theorems about evens and odds.

Feel free to suggest lemmas that should be added!

## Lemmas in the file

### contrapositive
`(p -> q) -> (~q -> ~p)`

### plus_n_0
`n + 0 = 0`

### plus_n_Sm
`n + (S m) = S (n + m)`

### plus_commutative
`n + m = m + n`

### plus_associative
`(n + m) + o = n + (m + o)`

### plus_reslut_0
`n + m = 0 <-> n = 0 /\ m = 0`

### mult_n_0
`n * 0 = 0`

### mult_1_n
`1 * n = n`

### mult_n_1
`n * 1 = n`

### mult_n_Sm
`n * (S m) = n + n * m`

### mult_commutative
`n * m = m * n`

### mult_left_distributive
`n * (m + o) = n * m + n * o`

### mult_right_distributive
`(n + m) * o = n * o + m * o`

### mult_associative
`(n * m) * o = n * (m * o)`

### mult_result_0
`n * m = 0 <-> n = 0 \/ m = 0`

### even_n__even_SSn
`even n -> even (S (S n))`

### odd_n__odd_SSn
`odd n -> odd (S (S n))`

### even_SSn__even_n
`even (S (S n)) -> even n`

### odd_SSn__odd_n
`odd (S (S n)) -> odd n`

### even_n__not_odd_n
`even n -> ~odd n`

### odd_n__not_even_n
`odd n -> ~even n`

### even_n__odd_Sn
`even n -> odd (S n)`

### odd_n__even_Sn
`odd n -> even (S n)`

### odd_n__not_odd_Sn
`odd n -> ~odd (S n)`

### even_n__not_even_Sn
`even n -> ~even (S n)`

### even_Sn__odd_n
`even (S n) -> odd n`

### odd_Sn__even_n
`odd (S n) -> even n`

### even_Sn__not_even_n
`even (S n) -> ~even n`

### odd_Sn__not_odd_n
`odd (S n) -> ~odd n`

### not_odd_n__odd_Sn
`~odd n -> odd (S n)`

### not_even_n__even_Sn
`~even n -> even (S n)`

### not_odd_n__even_n
`~odd n -> even n`

### not_even_n__odd_n
`~even n -> odd n`

### not_odd_Sn__odd_n
`~odd (S n) -> odd n`

### not_even_Sn__even_n
`~even (S n) -> even n`

### nat_odd_or_even
`even n \/ odd n`

### odd_n__even__n__false
`odd n /\ even n -> False`

### even_n__even_m__even_plus_n_m
`even n /\ even m -> even (n + m)`

### even_plus_n_m__even_n__even_m
`even (n + m) /\ even n -> even m`

### even_plus_n_m__even_m__even_n
`even (n + m) /\ even m -> even n`

### odd_n__odd_m__even_plus_n_m
`odd n /\ odd m -> even (n + m)`

### even_plus_n_m__odd_n__odd_m
`even (n + m) /\ odd_n -> odd m`

### even_plus_n_m__odd_m__odd_n
`even (n + m) /\ odd m -> odd n`

### even_n__odd_m__odd_plus_n_m
`even n /\ odd_m -> odd (n + m)`

### odd_plus_n_m__even_n__odd_m
`odd (n + m) /\ even n -> odd m`

### odd_plus_n_m__odd_m__even_n
`odd (n + m) /\ odd m -> even n`

### odd_n__even_m__odd_plus_n_m
`odd n /\ even m -> odd (n + m)`

### odd_plus_n_m__odd_n__even_m
`odd (n + m) /\ odd n -> even m`

### odd_plus_n_m__even_m__odd_n
`odd (n + m) /\ even m -> odd m`

### even_plus_n_n
`even (n + n)`

### even_plus_n_m_iff_even_n__odd_n_or_odd_n__odd_m
`even (n + m) <-> (even n /\ even m) \/ (odd n /\ odd m)`

### odd_plus_n_m_iff_even_n__odd_m_or_odd_n__even_m
`odd (n + m) <-> (even n /\ odd m) \/ (odd n /\ even m)`

### even_nSn
`even (n * S n)`

### even_n__even_nm
`even n -> even (n * m)`

### even_m__even_nm
`even m -> even (n * m)`

### even_nm__odd_n__even_m
`even (n * m) /\ odd n -> even m`

### even_nm__odd_m__even_n

`even (n * m) /\ odd m -> even n`

### even_nm_iff_even_n_or_even_m
`even (n * m) <-> even n \/ even m`

### odd_n__odd_m__odd_nm
`odd n /\ odd m -> odd (n * m)`

### odd_nm_iff_odd_n__odd_m
`odd (n * m) <-> odd n /\ odd m`

### power_n_1
`power n 1 = n`

### even_power_iff_even
`even (power n (S k)) <-> even n`

### odd_power_iff_odd
`odd (power n (S k)) <-> odd n`

### even_n_iff_plus_k_k
`even n <-> (exists k, n = k + k)`

### odd_n_iff_Splus_k_k
`odd n <-> (exists k, n = S (k + k))`

## LICENSE

Copyright 2019 qawbecrtey

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
