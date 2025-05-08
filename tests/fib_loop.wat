(module
  (func $fib (param $n i32) (result i32)
    (local $prev i32)
    (local $new i32)

    i32.const 0
    i32.const 1
    loop (param i32) (param i32) (result i32)
      ;; Return early if n is 0 or 1
      i32.const 2
      local.get $n
      i32.gt_u
      br_if 1

      local.tee $prev
      i32.add
      local.set $new

      ;; Decrement n
      local.get $n
      i32.const 1
      i32.sub
      local.set $n

      ;; Place old before new
      local.get $prev
      local.get $new

      br 0
    end
  )

  (export "fib" (func $fib))
)
