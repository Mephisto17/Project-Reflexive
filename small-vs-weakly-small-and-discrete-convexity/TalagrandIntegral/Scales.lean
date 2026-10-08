import TalagrandIntegral.MeanColor

set_option autoImplicit false

open Finset Classical
namespace TalagrandIntegral
noncomputable section

def scaleSum (n : ℕ) : ℝ := ∑ i : Fin n, (256:ℝ)^(i.val+1)

theorem scaleSum_succ (n : ℕ) : scaleSum (n+1) = scaleSum n + 256^(n+1) := by
  simp [scaleSum, Fin.sum_univ_castSucc]

theorem scaleSum_lower (n : ℕ) : (n:ℝ) ≤ scaleSum n := by
  calc
    (n:ℝ) = ∑ _ : Fin n, (1:ℝ) := by simp
    _ ≤ scaleSum n := Finset.sum_le_sum (fun i _ => one_le_pow₀ (by norm_num))

theorem scaleSum_upper (n : ℕ) : scaleSum n ≤ 2*(256:ℝ)^n := by
  induction n with
  | zero => norm_num [scaleSum]
  | succ n ih =>
    rw [scaleSum_succ, pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤256) n]

theorem exists_scale {p : ℝ} (hp : 0<p) :
    ∃ s : ℕ, p*scaleSum s ≤ 1/2 ∧ 1/2 < p*scaleSum (s+1) := by
  have hex : ∃ n : ℕ, 1/2 < p*scaleSum n := by
    obtain ⟨n,hn⟩ := exists_nat_gt (1/(2*p))
    have hn' : 1/2 < p*(n:ℝ) := by
      have h := (div_lt_iff₀ (by positivity : 0<2*p)).mp hn
      nlinarith
    exact ⟨n,hn'.trans_le (mul_le_mul_of_nonneg_left (scaleSum_lower n) hp.le)⟩
  let n := Nat.find hex
  have hn : 1/2 < p*scaleSum n := Nat.find_spec hex
  have hn0 : n ≠ 0 := by intro h; rw [h] at hn; norm_num [scaleSum] at hn
  obtain ⟨s,hs⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  refine ⟨s, ?_, ?_⟩
  · have hlt : s < Nat.find hex := by change s<n; omega
    exact le_of_not_gt (Nat.find_min hex hlt)
  · simpa [hs] using hn

def colorY {s : ℕ} (c : Fin (s+1)) : ℝ := (512:ℝ)^4 / (512:ℝ)^(c.val+1)

theorem colorY_pos {s : ℕ} (c : Fin (s+1)) : 0 < colorY c := by
  unfold colorY; positivity

theorem colorY_mean {p : ℝ} (hp : 0<p) {s : ℕ}
    (hs : p*scaleSum s ≤ 1/2) (hnext : 1/2 < p*scaleSum (s+1)) :
    (∑ c : Fin (s+1), colorProb p s c * colorY c) ≤ 5*(512:ℝ)^4*p := by
  have htail : 1/(512:ℝ)^(s+1) ≤ 4*p := by
    have h1 := mul_le_mul_of_nonneg_left (scaleSum_upper (s+1)) hp.le
    have h2 : (256:ℝ)^(s+1) ≤ (512:ℝ)^(s+1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    apply (div_le_iff₀ (by positivity : 0<(512:ℝ)^(s+1))).mpr
    nlinarith
  have hlast0 : 0 ≤ colorProb p s (Fin.last s) := (colorProb_pos hp hs _).le
  have hlast1 : colorProb p s (Fin.last s) ≤ 1 := by
    rw [colorProb_last]
    have h0 : 0 ≤ scaleSum s := (Nat.cast_nonneg s).trans (scaleSum_lower s)
    change 1-p*scaleSum s ≤ 1
    nlinarith
  have hlast : colorProb p s (Fin.last s)*colorY (Fin.last s) ≤ 4*(512:ℝ)^4*p := by
    calc
      _ ≤ colorY (Fin.last s) := mul_le_of_le_one_left (colorY_pos _).le hlast1
      _ = (512:ℝ)^4 * (1/(512:ℝ)^(s+1)) := by simp [colorY, div_eq_mul_inv]
      _ ≤ (512:ℝ)^4*(4*p) := mul_le_mul_of_nonneg_left htail (by positivity)
      _ = _ := by ring
  have he (i : Fin s) : colorProb p s i.castSucc * colorY i.castSucc =
      (512:ℝ)^4*p*(1/2:ℝ)^(i.val+1) := by
    rw [colorProb_early]
    simp only [colorY, Fin.val_castSucc]
    have hpow : (256:ℝ)^(i.val+1)/(512:ℝ)^(i.val+1) = (1/2:ℝ)^(i.val+1) := by
      rw [← div_pow]; norm_num
    rw [← hpow]; ring
  rw [Fin.sum_univ_castSucc]
  simp_rw [he, ← Finset.mul_sum]
  have hgeom : (∑ i : Fin s, (1/2:ℝ)^(i.val+1)) ≤ 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (1/2:ℝ)^(i+1)) s]
    have h := geom_positive_sum_le (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1) s
    norm_num at h ⊢; exact h
  nlinarith [mul_le_mul_of_nonneg_left hgeom (show 0 ≤ (512:ℝ)^4*p by positivity)]

end
end TalagrandIntegral
