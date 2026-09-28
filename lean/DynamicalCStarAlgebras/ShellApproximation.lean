import DynamicalCStarAlgebras.SchurApproximation

noncomputable section

namespace DynamicalCStarAlgebras

/-- Partition a finite sum into unit-width distance shells. -/
theorem finite_sum_shell_bound {X : Type*} (s : Finset X) (d f : X → ℝ) (b : ℕ → ℝ)
    (hd : ∀ x ∈ s, 0 ≤ d x)
    (hb : ∀ (m : ℕ) (t : Finset X), (∀ x ∈ t, (m : ℝ) ≤ d x ∧ d x < m + 1) →
      ∑ x ∈ t, f x ≤ b m) :
    ∑ x ∈ s, f x ≤ ∑ m ∈ s.image (fun x => ⌊d x⌋₊), b m := by
  classical
  refine (Finset.sum_fiberwise_of_maps_to
    (fun x hx => Finset.mem_image_of_mem (fun x => ⌊d x⌋₊) hx) f).symm.trans_le
      (Finset.sum_le_sum fun m _ => hb m _ ?_)
  exact fun x hx => (Finset.mem_filter.mp hx).2 ▸
    ⟨Nat.floor_le (hd x (Finset.mem_filter.mp hx).1), Nat.lt_floor_add_one (d x)⟩

/-- A finite exceptional set of shells controls all sufficiently distant finite sums. -/
theorem finite_tail_sum_bound {X : Type*} (s : Finset X) (d f : X → ℝ) (b : ℕ → ℝ)
    (hd : ∀ x, 0 ≤ d x)
    (hb : ∀ (m : ℕ) (t : Finset X), (∀ x ∈ t, (m : ℝ) ≤ d x ∧ d x < m + 1) →
      ∑ x ∈ t, f x ≤ b m)
    (F : Finset ℕ) {ε : ℝ}
    (hF : ∀ t : Finset ℕ, Disjoint t F → ‖∑ m ∈ t, b m‖ < ε) :
    ∑ x ∈ s, (if ((F.sup id : ℕ) : ℝ) + 1 < d x then f x else 0) ≤ ε := by
  classical
  rw [← Finset.sum_filter]
  refine (finite_sum_shell_bound _ d f b (fun x _ => hd x) hb).trans
    ((le_abs_self _).trans (le_of_lt ?_))
  refine (show ‖∑ m ∈ _, b m‖ < ε from hF _ ?_)
  refine Finset.disjoint_left.mpr fun m hm hmF => ?_
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm
  linarith [Nat.lt_floor_add_one (d x), (Finset.mem_filter.mp hx).2,
    show (⌊d x⌋₊ : ℝ) ≤ ((F.sup id : ℕ) : ℝ) from
      Nat.cast_le.mpr (Finset.le_sup (f := id) hmF)]

/-- Summable unit-shell bounds give finite-propagation approximation in operator norm. -/
theorem uniformRoe_of_summable_shell_bounds {X : Type*} [PseudoMetricSpace X]
    (a : Operator X) {b : ℕ → ℝ} (hb : Summable b)
    (hrow : ∀ x (m : ℕ) (s : Finset X),
      (∀ y ∈ s, (m : ℝ) ≤ dist x y ∧ dist x y < m + 1) →
        ∑ y ∈ s, ‖matrixEntry a x y‖ ≤ b m)
    (hcol : ∀ y (m : ℕ) (s : Finset X),
      (∀ x ∈ s, (m : ℝ) ≤ dist x y ∧ dist x y < m + 1) →
        ∑ x ∈ s, ‖matrixEntry a x y‖ ≤ b m) :
    a ∈ uniformRoe (CoarseStructure.ofPseudoMetric X) := by
  refine uniformRoe_of_schur_tails a fun ε hε => ?_
  obtain ⟨F, hF⟩ := summable_iff_vanishing_norm.mp hb ε hε
  refine ⟨((F.sup id : ℕ) : ℝ) + 1, by positivity, ?_, ?_⟩
  · exact fun x s => by
      simpa only [matrixTail, apply_ite norm, norm_zero] using
        finite_tail_sum_bound s (dist x) (fun y => ‖matrixEntry a x y‖) b
          (fun _ => dist_nonneg) (hrow x) F hF
  · exact fun y s => by
      simpa only [matrixTail, apply_ite norm, norm_zero] using
        finite_tail_sum_bound s (fun x => dist x y) (fun x => ‖matrixEntry a x y‖) b
          (fun _ => dist_nonneg) (hcol y) F hF

end DynamicalCStarAlgebras
