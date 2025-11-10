import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.GroupTheory.PGroup
import Mathlib.Order.CompletePartialOrder

set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

open Subgroup

structure ElementaryAbelian (p : ℕ) (G : Type*) [Group G] extends Subgroup G where
  is_comm : IsMulCommutative toSubgroup
  orderOf_eq : ∀ h : toSubgroup, h ≠ 1 → orderOf h = p


def IsElementaryAbelian {G : Type*} [Group G] (p : ℕ) (H : Subgroup G) : Prop :=
  IsMulCommutative H ∧ ∀ h : H, h ≠ 1 → orderOf h = p

namespace IsElementaryAbelian

lemma dvd_card {G : Type*} [Group G] {p : ℕ} {H : Subgroup G}
  [Finite H] (hH : IsElementaryAbelian p H) (bot_lt_H: ⊥ < H) : p ∣ (Nat.card H) := by
  simp [@SetLike.lt_iff_le_and_exists] at bot_lt_H
  obtain ⟨h, h_in_H, h_ne_one⟩ := bot_lt_H
  have order_eq_p : @orderOf H _ ⟨h, h_in_H⟩ = p := by
    apply hH.right ⟨h, h_in_H⟩
    simp [h_ne_one]
  rw [← order_eq_p]
  let inst : Fintype (H :) := Fintype.ofFinite ↥H
  have order_dvd_card := @orderOf_dvd_card H _ _ ⟨h, h_in_H⟩
  simp at order_dvd_card ⊢
  exact order_dvd_card


lemma primeFac_eq {G : Type*} [Group G] (p : ℕ)
  (hp : Nat.Prime p) (H : Subgroup G) [Finite H] (hH : IsElementaryAbelian p H) (bot_lt_H : ⊥ < H):
  Nat.primeFactors (Nat.card H) = {p} := by
  rw [@Finset.Subset.antisymm_iff]
  constructor
  -- Suppose the set of prime factors is not contained in {p}
  · by_contra! h
    rw [@Finset.not_subset] at h
    obtain ⟨q, hq, q_ne_p⟩ := h
    simp [← ne_eq] at q_ne_p
    rw [Nat.mem_primeFactors] at hq
    obtain ⟨hq, q_dvd_card, -⟩ := hq
    let Fintype_H : Fintype H := Fintype.ofFinite ↥H
    simp at q_dvd_card
    obtain ⟨x, order_eq_q⟩ := @exists_prime_orderOf_dvd_card H _ _ q ({out := hq}) q_dvd_card
    have q_ne_one : q ≠ 1 := Nat.Prime.ne_one hq
    have x_ne_one : x ≠ 1 := by
      intro h
      rw [← orderOf_eq_one_iff, order_eq_q] at h
      contradiction
    have order_eq_p : orderOf x = p := hH.right x x_ne_one
    absurd q_ne_p (order_eq_q ▸ order_eq_p)
    trivial
  · simp
    exact
      ⟨hp, dvd_card hH bot_lt_H, Nat.ne_zero_iff_zero_lt.mpr Nat.card_pos⟩



lemma IsPGroup {G : Type*} [hG : Group G] (p : ℕ) (hp : Nat.Prime p)
  (H : Subgroup G) [hH₀ : Finite H] (hH : IsElementaryAbelian p H) (bot_lt_H : ⊥ < H):
  IsPGroup p H := by
  let hp' : Fact (Nat.Prime p) := { out := hp }
  rw [IsPGroup.iff_card]
  have : Nat.primeFactors (Nat.card (H :)) = {p} :=
    @primeFac_eq G _ p hp H _ hH bot_lt_H
  have card_primeFac_eq_one : (Nat.card ↥H).primeFactors.card = 1 := this ▸ rfl
  have card_eq_isPrimePow :=
    (@isPrimePow_iff_card_primeFactors_eq_one (Nat.card (H :))).mpr card_primeFac_eq_one
  rw [isPrimePow_nat_iff] at card_eq_isPrimePow
  obtain ⟨p', k, hp', zero_lt_k, card_eq⟩ := card_eq_isPrimePow
  have p'_dvd_card : p' ∣ Nat.card H :=
    card_eq.symm ▸ Dvd.dvd.pow (dvd_refl p') (ne_of_gt zero_lt_k)
  have p_eq_p' : p' ∈ (Nat.card ↥H).primeFactors := by
    rw [@Nat.mem_primeFactors]
    exact ⟨hp', p'_dvd_card, Nat.ne_zero_iff_zero_lt.mpr Nat.card_pos⟩
  simp [this] at p_eq_p'
  use k, p_eq_p'▸ card_eq.symm


lemma subgroupOf {G : Type*} [Group G]
  (H K : Subgroup G) {p : ℕ} [Fact (Nat.Prime p)] (hH : IsElementaryAbelian p H) :
  IsElementaryAbelian p (H.subgroupOf K) := by
  refine ⟨?IsMulCommutative, ?orderOf_eq_p⟩
  case IsMulCommutative =>
    let IsCommutative_H : IsMulCommutative H := hH.left
    exact subgroupOf_isMulCommutative K H
  case orderOf_eq_p =>
    rintro ⟨h, hh⟩ h_ne_one
    have h_in_H := hh
    simp [mem_subgroupOf] at h_in_H
    have h_ne_one' : ⟨(h : G), h_in_H⟩ ≠ (1 : H) := by
      simp
      rintro rfl
      simp_all
    have order_of_eq_p' := hH.right ⟨(h : G), h_in_H⟩ h_ne_one'
    simp [← order_of_eq_p']

end IsElementaryAbelian
