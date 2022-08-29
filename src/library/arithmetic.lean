/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import algebra.order.ring


section
variables {α : Type*} [linear_ordered_semiring α]

lemma pos_of_mul_pos_right' {b : α} (a : α) (h : 0 < a * b) (ha : 0 ≤ a) : 0 < b  :=
pos_of_mul_pos_right h ha

lemma nonneg_of_mul_nonneg_right' {b : α} (a : α) (h : 0 ≤ a * b) (ha : 0 < a) : 0 ≤ b :=
nonneg_of_mul_nonneg_right h ha

lemma nonpos_of_mul_nonneg_right' {b : α} (a : α) (h : 0 ≤ a * b) (ha : a < 0) : b ≤ 0 :=
nonpos_of_mul_nonneg_right h ha

lemma nonpos_of_mul_nonpos_right' {b : α} (a : α) (h : a * b ≤ 0) (ha : 0 < a) : b ≤ 0 :=
nonpos_of_mul_nonpos_right h ha

end


section
variables {α : Type*} [linear_ordered_ring α]

lemma nonneg_of_mul_nonpos_right' {b : α} (a : α) (h : a * b ≤ 0) (ha : a < 0) : 0 ≤ b :=
nonneg_of_mul_nonpos_right h ha

end