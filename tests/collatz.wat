(module
    ;; Calculate the number of steps of the Collatz conjecture to reach 1
    (func $collatz (param $n i32) (result i32)
        i32.const 0
        loop (param i32) (result i32)
            ;; Exit if n is 0 or 1
            (i32.gt_u (i32.const 2) (local.get $n))
            br_if 1

            ;; Halve n if it's even,
            ;; multiply by 3 and add 1 if it's odd
            (if (result i32)
                (i32.and (local.get $n) (i32.const 1))
                (then
                    ;; n is odd
                    (i32.add
                        (i32.mul (local.get $n) (i32.const 3))
                        (i32.const 1)
                    )
                )
                (else
                    ;; n is even
                    (i32.shr_u (local.get $n) (i32.const 1))
                )
            )
            (local.set $n)

            ;; Increment the counter
            (i32.const 1)
            i32.add

            br 0
        end
    )
    
    (export "collatz" (func $collatz))
)
