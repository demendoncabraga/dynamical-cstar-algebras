import DynamicalCStarAlgebras.PartialTranslationPartition
import DynamicalCStarAlgebras.QuasiLocalContinuity
import DynamicalCStarAlgebras.CoarseContinuity
import DynamicalCStarAlgebras.ValleePoussin

noncomputable section
namespace DynamicalCStarAlgebras
open Classical

/-- Uniform finite row bounds for a relation. -/
def HasUniformFiniteRows {X : Type*} (E : Set (X × X)) : Prop :=
  ∃ N : ℕ, ∀ x, {y | (x, y) ∈ E}.Finite ∧ {y | (x, y) ∈ E}.ncard ≤ N

lemma HasUniformFiniteRows.subset {X : Type*} {E F : Set (X × X)}
    (hF : HasUniformFiniteRows F) (hEF : E ⊆ F) : HasUniformFiniteRows E := by
  obtain ⟨N, hN⟩ := hF
  refine ⟨N, fun x => ⟨(hN x).1.subset (fun _ hy => hEF hy), ?_⟩⟩
  exact (Set.ncard_le_ncard (show {y | (x, y) ∈ E} ⊆ {y | (x, y) ∈ F} from fun _ hy => hEF hy) (hN x).1).trans (hN x).2

lemma HasUniformFiniteRows.union {X : Type*} {E F : Set (X × X)}
    (hE : HasUniformFiniteRows E) (hF : HasUniformFiniteRows F) : HasUniformFiniteRows (E ∪ F) := by
  obtain ⟨N, hN⟩ := hE
  obtain ⟨M, hM⟩ := hF
  refine ⟨N + M, fun x => ?_⟩
  change ({y | (x, y) ∈ E} ∪ {y | (x, y) ∈ F}).Finite ∧ _
  refine ⟨(hN x).1.union (hM x).1, ?_⟩
  exact Set.ncard_union_le _ _ |>.trans (Nat.add_le_add (hN x).2 (hM x).2)

lemma HasUniformFiniteRows.comp {X : Type*} {E F : Set (X × X)}
    (hE : HasUniformFiniteRows E) (hF : HasUniformFiniteRows F) :
    HasUniformFiniteRows {p | ∃ z, (p.1, z) ∈ E ∧ (z, p.2) ∈ F} := by
  obtain ⟨N, hN⟩ := hE
  obtain ⟨M, hM⟩ := hF
  refine ⟨N * M, fun x => ?_⟩
  let s := (hN x).1.toFinset
  have he : {y | (x, y) ∈ {p | ∃ z, (p.1, z) ∈ E ∧ (z, p.2) ∈ F}} =
      ⋃ z ∈ s, {y | (z, y) ∈ F} := by
    ext y
    simp [s]
  rw [he]
  refine ⟨s.finite_toSet.biUnion (fun z _ => (hM z).1), ?_⟩
  calc
    _ ≤ ∑ z ∈ s, {y | (z, y) ∈ F}.ncard := s.set_ncard_biUnion_le _
    _ ≤ ∑ _z ∈ s, M := Finset.sum_le_sum fun z _ => (hM z).2
    _ = s.card * M := by simp
    _ ≤ N * M := Nat.mul_le_mul_right M (by
      dsimp [s]
      rw [← Set.ncard_eq_toFinset_card {y | (x, y) ∈ E} (hN x).1]
      exact (hN x).2)

/-- The largest uniformly locally finite coarse structure on an arbitrary set. -/
def maximalUniformlyLocallyFinite (X : Type*) : CoarseStructure X where
  controlled := {E | HasUniformFiniteRows E ∧ HasUniformFiniteRows {p | (p.2, p.1) ∈ E}}
  diagonal := by
    have hd : HasUniformFiniteRows {p : X × X | p.1 = p.2} :=
      ⟨1, fun x => by simp [Set.mem_ofPred_eq]⟩
    exact ⟨hd, by simpa only [Set.mem_ofPred_eq, eq_comm] using hd⟩
  subset := fun hEF hF => ⟨hF.1.subset hEF, hF.2.subset (fun _ hp => hEF hp)⟩
  union := fun hE hF => ⟨hE.1.union hF.1, hE.2.union hF.2⟩
  inverse := fun hE => ⟨hE.2, hE.1⟩
  comp := fun hE hF => ⟨hE.1.comp hF.1, by
    simpa only [Set.mem_ofPred_eq, and_comm] using hF.2.comp hE.2⟩

lemma maximalUniformlyLocallyFinite_ulf (X : Type*) :
    (maximalUniformlyLocallyFinite X).UniformlyLocallyFinite :=
  fun _ hE _ => hE.1

lemma maximalUniformlyLocallyFinite_maximal {X : Type*} (C : CoarseStructure X)
    (hC : C.UniformlyLocallyFinite) : C.IsSubstructure (maximalUniformlyLocallyFinite X) :=
  fun _ hE => ⟨hC.fiber_bounds hE, hC.fiber_bounds (C.inverse hE)⟩

lemma matching_mem_maximalUniformlyLocallyFinite {X I : Type*} (f g : I → X)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Set.range (fun i => (f i, g i)) ∈ (maximalUniformlyLocallyFinite X).controlled := by
  have hr (f g : I → X) (hf : Function.Injective f) :
      HasUniformFiniteRows (Set.range (fun i => (f i, g i))) := by
    refine ⟨1, fun x => ?_⟩
    have hs : {y | (x, y) ∈ Set.range (fun i => (f i, g i))}.Subsingleton := by
      rintro y ⟨i, hi⟩ z ⟨j, hj⟩
      have hij : i = j := hf ((congrArg Prod.fst hi).trans (congrArg Prod.fst hj).symm)
      exact (congrArg Prod.snd hi).symm.trans ((congrArg g hij).trans (congrArg Prod.snd hj))
    exact ⟨hs.finite, (Set.ncard_le_one hs.finite).mpr (fun _ h₁ _ h₂ => hs h₁ h₂)⟩
  refine ⟨hr f g hf, ?_⟩
  have he : {p : X × X | (p.2, p.1) ∈ Set.range (fun i => (f i, g i))} =
      Set.range (fun i => (g i, f i)) := by
    ext p
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, Prod.swap_inj.mpr hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, Prod.swap_inj.mp hi⟩
  rw [he]
  exact hr g f hg

/-- On the maximal uniformly locally finite structure, every coarse real map is bounded. -/
theorem isCoarseReal_maximalUniformlyLocallyFinite_iff {X : Type*} (h : X → ℝ) :
    IsCoarseReal (maximalUniformlyLocallyFinite X) h ↔ ∃ M : ℝ, ∀ x, |h x| ≤ M := by
  constructor
  · intro hc
    by_contra hn
    push Not at hn
    choose pick hpick using hn
    let u : ℕ → X := fun n => Nat.rec (pick 0)
      (fun k x => pick (|h x| + (k : ℝ) + 1)) n
    have hstep (n : ℕ) : |h (u n)| + (n : ℝ) + 1 < |h (u (n + 1))| :=
      hpick (|h (u n)| + (n : ℝ) + 1)
    have hmono : StrictMono (fun n => |h (u n)|) := strictMono_nat_of_lt_succ
      (fun n => lt_of_le_of_lt (by linarith [show (0 : ℝ) ≤ n by positivity]) (hstep n))
    have hu : Function.Injective u := fun i j hij => hmono.injective (congrArg (fun x => |h x|) hij)
    let f : ℕ → X := fun n => u (2 * n)
    let g : ℕ → X := fun n => u (2 * n + 1)
    have hf : Function.Injective f := fun i j hij => by
      dsimp [f] at hij
      have hh := hu hij
      omega
    have hg : Function.Injective g := fun i j hij => by
      dsimp [g] at hij
      have hh := @hu (2 * i + 1) (2 * j + 1) hij
      omega
    obtain ⟨R, hR⟩ := hc _ (matching_mem_maximalUniformlyLocallyFinite f g hf hg)
    obtain ⟨n, hn⟩ := exists_nat_gt R
    have hr := hR (f n, g n) (Set.mem_range_self n)
    rw [Real.dist_eq] at hr
    have hdiff := abs_sub_abs_le_abs_sub (h (g n)) (h (f n))
    rw [abs_sub_comm (h (g n)) (h (f n))] at hdiff
    have hs := hstep (2 * n)
    change |h (f n)| + ((2 * n : ℕ) : ℝ) + 1 < |h (g n)| at hs
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hs
    linarith [show (0 : ℝ) ≤ n by positivity]
  · rintro ⟨M, hM⟩ E _hE
    refine ⟨2 * M, fun p _ => ?_⟩
    rw [Real.dist_eq]
    exact (abs_sub _ _).trans (by linarith [hM p.1, hM p.2])

lemma continuityPoints_eq_univ_of_bounded {X : Type*} (h : X → ℝ)
    (hb : ∃ M : ℝ, ∀ x, |h x| ≤ M) : continuityPoints h = Set.univ := by
  obtain ⟨M, hM⟩ := hb
  apply Set.eq_univ_of_forall
  intro a
  apply finitePropagation_mem_continuityPoints h a
  refine ⟨2 * max M 0 + 1, by positivity, fun x y hxy => ?_⟩
  have hd : dist (h x) (h y) ≤ 2 * max M 0 + 1 := by
    rw [Real.dist_eq]
    exact (abs_sub _ _).trans (by linarith [hM x, hM y, le_max_left M 0])
  exact False.elim (not_lt_of_ge hd (by
    simpa only [realPullbackPseudoMetric_dist] using hxy))

/-- Every bounded operator is a simultaneous continuity point for the maximal structure. -/
theorem coarseContinuityPoints_maximalUniformlyLocallyFinite (X : Type*) :
    coarseContinuityPoints (maximalUniformlyLocallyFinite X) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro a h hc
  rw [continuityPoints_eq_univ_of_bounded h
    ((isCoarseReal_maximalUniformlyLocallyFinite_iff h).mp hc)]
  exact Set.mem_univ a

end DynamicalCStarAlgebras
