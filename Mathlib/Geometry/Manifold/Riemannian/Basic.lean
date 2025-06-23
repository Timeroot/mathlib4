/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! # Riemannian manifolds

A Riemannian manifold `M` is a real manifold such that its tangent spaces are endowed with a
scalar product, depending smoothly on the point, and such that `M` has an emetric space
structure for which the distance is the infimum of lengths of paths. -/

open Bundle Bornology Set MeasureTheory
open scoped Manifold ENNReal ContDiff Topology

local notation "⟪" x ", " y "⟫" => inner ℝ x y

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

instance (x : ℝ) : One (TangentSpace 𝓘(ℝ) x) where
  one := (1 : ℝ)

/-- Unit vector in the tangent space to a segment, as the image of the unit vector in the real line
under the canonical projection. It is also mapped to the unit vector in the real line through
the canonical injection, see `mfderiv_subtypeVal_Icc_one`.

Note that one can not abuse defeqs for this definition: this is *not* the same as the vector
`fun _ ↦ 1` in `EuclideanSpace ℝ (Fin 1)` through defeqs, as one of the charts of `Icc x y` is
orientation-reversing. -/
irreducible_def one_tangentSpace_Icc {x y : ℝ} [h : Fact (x < y)] (z : Icc x y) :
    TangentSpace (𝓡∂ 1) z :=
  mfderivWithin 𝓘(ℝ) (𝓡∂ 1) (Set.projIcc x y h.out.le) (Icc x y) z 1

instance {x y : ℝ} [h : Fact (x < y)] (z : Icc x y) : One (TangentSpace (𝓡∂ 1) z) where
  one := one_tangentSpace_Icc z

set_option says.verify true

section ToMove

variable {x y : ℝ} [h : Fact (x < y)] {n : WithTop ℕ∞}

/-- The inclusion map from of a closed segment to `ℝ` is smooth in the manifold sense. -/
lemma contMDiff_subtypeVal_Icc  :
    ContMDiff (𝓡∂ 1) 𝓘(ℝ) n (fun (z : Icc x y) ↦ (z : ℝ)) := by
  intro z
  rw [contMDiffAt_iff]
  refine ⟨by fun_prop, ?_⟩
  simp? says
    simp only [extChartAt, PartialHomeomorph.extend, PartialHomeomorph.refl_partialEquiv,
      PartialEquiv.refl_source, PartialHomeomorph.singletonChartedSpace_chartAt_eq,
      modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl, PartialEquiv.refl_coe,
      Icc_chartedSpaceChartAt, PartialEquiv.coe_trans_symm, PartialHomeomorph.coe_coe_symm,
      ModelWithCorners.toPartialEquiv_coe_symm, CompTriple.comp_eq, PartialEquiv.coe_trans,
      ModelWithCorners.toPartialEquiv_coe, PartialHomeomorph.toFun_eq_coe, Function.comp_apply]
  split_ifs with hz
  · simp? [IccLeftChart, Function.comp_def, modelWithCornersEuclideanHalfSpace] says
      simp only [IccLeftChart, Fin.isValue, PartialHomeomorph.mk_coe_symm, PartialEquiv.coe_symm_mk,
      modelWithCornersEuclideanHalfSpace, ModelWithCorners.mk_symm, Function.comp_def,
      Function.update_self, ModelWithCorners.mk_coe, PartialHomeomorph.mk_coe]
    rw [Subtype.range_val_subtype]
    have : ContDiff ℝ n (fun (z : EuclideanSpace ℝ (Fin 1)) ↦ z 0 + x) := by fun_prop
    apply this.contDiffWithinAt.congr_of_eventuallyEq_of_mem; swap
    · simpa using z.2.1
    have : {w : EuclideanSpace ℝ (Fin 1) | w 0 < y - x} ∈ 𝓝 (fun i ↦ z - x) := by
      apply (isOpen_lt (continuous_apply 0) continuous_const).mem_nhds
      simpa using hz
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds this] with w hw h'w
    rw [max_eq_left hw, min_eq_left]
    linarith
  · simp only [not_lt] at hz
    simp? [IccRightChart, Function.comp_def, modelWithCornersEuclideanHalfSpace] says
      simp only [IccRightChart, Fin.isValue, PartialHomeomorph.mk_coe_symm,
        PartialEquiv.coe_symm_mk, modelWithCornersEuclideanHalfSpace, ModelWithCorners.mk_symm,
        Function.comp_def, Function.update_self, ModelWithCorners.mk_coe, PartialHomeomorph.mk_coe]
    rw [Subtype.range_val_subtype]
    have : ContDiff ℝ n (fun (z : EuclideanSpace ℝ (Fin 1)) ↦ y - z 0) := by fun_prop
    apply this.contDiffWithinAt.congr_of_eventuallyEq_of_mem; swap
    · simpa using z.2.2
    have : {w : EuclideanSpace ℝ (Fin 1) | w 0 < y - x} ∈ 𝓝 (fun i ↦ y - z) := by
      apply (isOpen_lt (continuous_apply 0) continuous_const).mem_nhds
      simpa using h.out.trans_le hz
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds this] with w hw h'w
    rw [max_eq_left hw, max_eq_left]
    linarith

/-- The projection from `ℝ` to a closed segment is smooth on the segment, in the manifold sense. -/
lemma contMDiffOn_projIcc :
    ContMDiffOn 𝓘(ℝ) (𝓡∂ 1) n (Set.projIcc x y h.out.le) (Icc x y) := by
  intro z hz
  rw [contMDiffWithinAt_iff]
  refine ⟨by apply ContinuousAt.continuousWithinAt; fun_prop, ?_⟩
  simp? says
    simp only [extChartAt, PartialHomeomorph.extend, Icc_chartedSpaceChartAt,
      PartialEquiv.coe_trans, ModelWithCorners.toPartialEquiv_coe, PartialHomeomorph.toFun_eq_coe,
      PartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_source,
      PartialHomeomorph.singletonChartedSpace_chartAt_eq, modelWithCornersSelf_partialEquiv,
      PartialEquiv.trans_refl, PartialEquiv.refl_symm, PartialEquiv.refl_coe, CompTriple.comp_eq,
      preimage_id_eq, id_eq, modelWithCornersSelf_coe, range_id, inter_univ]
  split_ifs with h'z
  · simp? [IccLeftChart, Function.comp_def, modelWithCornersEuclideanHalfSpace, projIcc] says
      simp only [modelWithCornersEuclideanHalfSpace, Fin.isValue, ModelWithCorners.mk_coe,
        IccLeftChart, PartialHomeomorph.mk_coe, Function.comp_def, projIcc]
    have : ContDiff ℝ n (fun (w : ℝ) ↦
        (show EuclideanSpace ℝ (Fin 1) from fun (_ : Fin 1) ↦ w - x)) := by
      dsimp
      apply contDiff_euclidean.2 (fun i ↦ by fun_prop)
    apply this.contDiffWithinAt.congr_of_eventuallyEq_of_mem _ hz
    filter_upwards [self_mem_nhdsWithin] with w hw
    ext i
    simp only [sub_left_inj]
    rw [max_eq_right, min_eq_right hw.2]
    simp [hw.1, h.out.le]
  · simp? [IccRightChart, Function.comp_def, modelWithCornersEuclideanHalfSpace, projIcc] says
      simp only [modelWithCornersEuclideanHalfSpace, Fin.isValue, ModelWithCorners.mk_coe,
        IccRightChart, PartialHomeomorph.mk_coe, Function.comp_def, projIcc]
    have : ContDiff ℝ n (fun (w : ℝ) ↦
        (show EuclideanSpace ℝ (Fin 1) from fun (_ : Fin 1) ↦ y - w)) := by
      dsimp
      apply contDiff_euclidean.2 (fun i ↦ by fun_prop)
    apply this.contDiffWithinAt.congr_of_eventuallyEq_of_mem _ hz
    filter_upwards [self_mem_nhdsWithin] with w hw
    ext i
    simp only [sub_left_inj]
    rw [max_eq_right, min_eq_right hw.2]
    simp [hw.1, h.out.le]

lemma contMDiffOn_comp_projIcc_iff {f : Icc x y → M} :
    ContMDiffOn 𝓘(ℝ) I n (f ∘ (Set.projIcc x y h.out.le)) (Icc x y) ↔ ContMDiff (𝓡∂ 1) I n f := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ hf.comp_contMDiffOn contMDiffOn_projIcc⟩
  convert hf.comp_contMDiff (contMDiff_subtypeVal_Icc (x := x) (y := y)) (fun z ↦ z.2)
  ext z
  simp

lemma contMDiffWithinAt_comp_projIcc_iff {f : Icc x y → M} {w : Icc x y} :
    ContMDiffWithinAt 𝓘(ℝ) I n (f ∘ (Set.projIcc x y h.out.le)) (Icc x y) w ↔
      ContMDiffAt (𝓡∂ 1) I n f w := by
  refine ⟨fun hf ↦ ?_,
    fun hf ↦ hf.comp_contMDiffWithinAt_of_eq (contMDiffOn_projIcc w w.2) (by simp)⟩
  have A := contMDiff_subtypeVal_Icc (x := x) (y := y) (n := n) w
  rw [← contMDiffWithinAt_univ] at A ⊢
  convert hf.comp _ A (fun z hz ↦ z.2)
  ext z
  simp

lemma mdifferentiableWithinAt_comp_projIcc_iff {f : Icc x y → M} {w : Icc x y} :
    MDifferentiableWithinAt 𝓘(ℝ) I (f ∘ (Set.projIcc x y h.out.le)) (Icc x y) w ↔
      MDifferentiableAt (𝓡∂ 1) I f w := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · have A := (contMDiff_subtypeVal_Icc (x := x) (y := y) (n := 1) w).mdifferentiableAt le_rfl
    rw [← mdifferentiableWithinAt_univ] at A ⊢
    convert hf.comp _ A (fun z hz ↦ z.2)
    ext z
    simp
  · have := (contMDiffOn_projIcc (x := x) (y := y) (n := 1) w w.2).mdifferentiableWithinAt le_rfl
    exact MDifferentiableAt.comp_mdifferentiableWithinAt_of_eq (w : ℝ) hf this (by simp)

lemma mfderivWithin_projIcc_one {z : ℝ} (hz : z ∈ Icc x y) :
    mfderivWithin 𝓘(ℝ) (𝓡∂ 1) (Set.projIcc x y h.out.le) (Icc x y) z 1 = 1 := by
  change _ = one_tangentSpace_Icc (Set.projIcc x y h.out.le z)
  simp [one_tangentSpace_Icc]
  congr
  simp only [projIcc_of_mem h.out.le hz]

lemma mfderivWithin_comp_projIcc_one {f : Icc x y → M} {w : Icc x y} :
    mfderivWithin 𝓘(ℝ) I (f ∘ (projIcc x y h.out.le)) (Icc x y) w 1 = mfderiv (𝓡∂ 1) I f w 1 := by
  by_cases hw : MDifferentiableAt (𝓡∂ 1) I f w; swap
  · rw [mfderiv_zero_of_not_mdifferentiableAt hw, mfderivWithin_zero_of_not_mdifferentiableWithinAt]
    · rfl
    · rwa [mdifferentiableWithinAt_comp_projIcc_iff]
  rw [mfderiv_comp_mfderivWithin (I' := 𝓡∂ 1)]; rotate_left
  · convert hw
    simp
  · apply (contMDiffOn_projIcc _ w.2).mdifferentiableWithinAt le_rfl
  · apply (uniqueDiffOn_Icc h.out _ w.2).uniqueMDiffWithinAt
  simp only [Function.comp_apply, ContinuousLinearMap.coe_comp']
  have I : projIcc x y h.out.le (w : ℝ) = w := by rw [projIcc_of_mem]
  have J : w = projIcc x y h.out.le (w : ℝ) := by rw [I]
  rw [I]
  congr 1
  convert mfderivWithin_projIcc_one w.2

lemma mfderiv_subtype_coe_Icc_one (z : Icc x y) :
    mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc x y → ℝ) z 1 = 1 := by
  have A : mfderivWithin 𝓘(ℝ) 𝓘(ℝ) (Subtype.val ∘ (projIcc x y h.out.le)) (Icc x y) z 1
      = mfderivWithin 𝓘(ℝ) 𝓘(ℝ) id (Icc x y) z 1 := by
    congr 1
    apply mfderivWithin_congr_of_mem _ z.2
    intro z hz
    simp [projIcc_of_mem h.out.le hz]
  rw [← mfderivWithin_comp_projIcc_one, A]
  simp only [id_eq, mfderivWithin_eq_fderivWithin]
  rw [fderivWithin_id (uniqueDiffOn_Icc h.out _ z.2)]
  rfl

end ToMove

namespace Manifold

variable [∀ (x : M), ENorm (TangentSpace I x)] {x y : ℝ} {γ γ' : ℝ → M}

variable (I) in
/-- The length on `Icc x y` of a path into a manifold, where the path is defined on the whole real
line.

We use the whole real line to avoid subtype hell in API, but this is equivalent to
considering functions on the manifold with boundary `Icc x y`, see
`lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc`.

We use `mfderiv` instead of `mfderivWithin` in the definition as these coincide (apart from the two
endpoints which have zero measure) and `mfderiv` is easier to manipulate. However, we give
a lemma `pathELength_eq_integral_mfderivWithin_Icc` to rewrite with the `mfderivWithin` form. -/
irreducible_def pathELength (γ : ℝ → M) (x y : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Icc x y, ‖mfderiv 𝓘(ℝ) I γ t 1‖ₑ

lemma pathELength_eq_lintegral_mfderiv_Icc :
    pathELength I γ x y = ∫⁻ t in Icc x y, ‖mfderiv 𝓘(ℝ) I γ t 1‖ₑ := by simp [pathELength]

lemma pathELength_eq_lintegral_mfderiv_Ioo :
    pathELength I γ x y = ∫⁻ t in Ioo x y, ‖mfderiv 𝓘(ℝ) I γ t 1‖ₑ := by
  rw [pathELength_eq_lintegral_mfderiv_Icc, restrict_Ioo_eq_restrict_Icc]

lemma pathELength_eq_lintegral_mfderivWithin_Icc :
    pathELength I γ x y = ∫⁻ t in Icc x y, ‖mfderivWithin 𝓘(ℝ) I γ (Icc x y) t 1‖ₑ := by
  rw [pathELength_eq_lintegral_mfderiv_Icc, ← restrict_Ioo_eq_restrict_Icc]
  apply setLIntegral_congr_fun measurableSet_Ioo (fun t ht ↦ ?_)
  rw [mfderivWithin_of_mem_nhds]
  exact Icc_mem_nhds ht.1 ht.2

@[simp] lemma pathELength_self : pathELength I γ x x = 0 := by
  simp [pathELength]

lemma pathELength_congr (h : EqOn γ γ' (Icc x y)) : pathELength I γ x y = pathELength I γ' x y := by
  simp only [pathELength_eq_lintegral_mfderivWithin_Icc]
  apply setLIntegral_congr_fun measurableSet_Icc (fun t ht ↦ ?_)
  have A : γ t = γ' t := h ht
  congr! 2
  exact mfderivWithin_congr h A

lemma pathELength_eq_add {γ : ℝ → M} {x y z : ℝ} (h : x ≤ y) (h' : y ≤ z) :
    pathELength I γ x z = pathELength I γ x y + pathELength I γ y z := by
  have : Icc x z = Icc x y ∪ Ioc y z := (Icc_union_Ioc_eq_Icc h h').symm
  rw [pathELength, this, lintegral_union measurableSet_Ioc]; swap
  · exact disjoint_iff_forall_ne.mpr (fun a ha b hb ↦ (ha.2.trans_lt hb.1).ne)
  simp [restrict_Ioc_eq_restrict_Icc, pathELength]

attribute [local instance] Measure.Subtype.measureSpace

lemma lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc {x y : ℝ}
    [h : Fact (x < y)] {γ : Icc x y → M} :
    ∫⁻ t, ‖mfderiv (𝓡∂ 1) I γ t 1‖ₑ = pathELength I (γ ∘ (projIcc x y h.out.le)) x y := by
  rw [pathELength_eq_lintegral_mfderivWithin_Icc]
  simp_rw [← mfderivWithin_comp_projIcc_one]
  have : MeasurePreserving (Subtype.val : Icc x y → ℝ) volume
    (volume.restrict (Icc x y)) := measurePreserving_subtype_coe measurableSet_Icc
  rw [← MeasureTheory.MeasurePreserving.lintegral_comp_emb this
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
  congr
  ext t
  have : t = projIcc x y h.out.le (t : ℝ) := by simp
  congr

open MeasureTheory

variable [∀ (x : M), ENormSMulClass ℝ (TangentSpace I x)]

lemma pathELength_comp_of_monotoneOn {γ : ℝ → M} {f : ℝ → ℝ} {x y : ℝ} (h : x ≤ y)
    (hf : MonotoneOn f (Icc x y))
    (h'f : DifferentiableOn ℝ f (Icc x y)) (hγ : MDifferentiableOn 𝓘(ℝ) I γ (Icc (f x) (f y))) :
    pathELength I (γ ∘ f) x y = pathELength I γ (f x) (f y) := by
  rcases h.eq_or_lt with rfl | h
  · simp
  have f_im : f '' (Icc x y) = Icc (f x) (f y) := h'f.continuousOn.image_Icc_of_monotoneOn h.le hf
  simp only [pathELength_eq_lintegral_mfderivWithin_Icc, ← f_im]
  have B (t) (ht : t ∈ Icc x y) : HasDerivWithinAt f (derivWithin f (Icc x y) t) (Icc x y) t :=
    (h'f t ht).hasDerivWithinAt
  rw [lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn measurableSet_Icc B hf]
  apply setLIntegral_congr_fun measurableSet_Icc (fun t ht ↦ ?_)
  have : (mfderivWithin 𝓘(ℝ, ℝ) I (γ ∘ f) (Icc x y) t)
      = (mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc (f x) (f y)) (f t))
          ∘L mfderivWithin 𝓘(ℝ) 𝓘(ℝ) f (Icc x y) t := by
    rw [← f_im] at hγ ⊢
    apply mfderivWithin_comp
    · apply hγ _ (mem_image_of_mem _ ht)
    · rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
      exact h'f _ ht
    · exact subset_preimage_image _ _
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc h _ ht
  rw [this]
  simp only [Function.comp_apply, ContinuousLinearMap.coe_comp']
  have : mfderivWithin 𝓘(ℝ) 𝓘(ℝ) f (Icc x y) t 1
      = derivWithin f (Icc x y) t • (1 : TangentSpace 𝓘(ℝ) (f t)) := by
    simp only [mfderivWithin_eq_fderivWithin, ← fderivWithin_derivWithin, smul_eq_mul, mul_one]
    rfl
  rw [this]
  have : 0 ≤ derivWithin f (Icc x y) t := hf.derivWithin_nonneg
  simp only [map_smul, enorm_smul, ← Real.enorm_of_nonneg this, f_im]

lemma pathELength_comp_of_antitoneOn {γ : ℝ → M} {f : ℝ → ℝ} {x y : ℝ} (h : x ≤ y)
    (hf : AntitoneOn f (Icc x y))
    (h'f : DifferentiableOn ℝ f (Icc x y)) (hγ : MDifferentiableOn 𝓘(ℝ) I γ (Icc (f y) (f x))) :
    pathELength I (γ ∘ f) x y = pathELength I γ (f y) (f x) := by
  rcases h.eq_or_lt with rfl | h
  · simp
  have f_im : f '' (Icc x y) = Icc (f y) (f x) := h'f.continuousOn.image_Icc_of_antitoneOn h.le hf
  simp only [pathELength_eq_lintegral_mfderivWithin_Icc, ← f_im]
  have B (t) (ht : t ∈ Icc x y) : HasDerivWithinAt f (derivWithin f (Icc x y) t) (Icc x y) t :=
    (h'f t ht).hasDerivWithinAt
  rw [lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn measurableSet_Icc B hf]
  apply setLIntegral_congr_fun measurableSet_Icc (fun t ht ↦ ?_)
  have : (mfderivWithin 𝓘(ℝ, ℝ) I (γ ∘ f) (Icc x y) t)
      = (mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc (f y) (f x)) (f t))
          ∘L mfderivWithin 𝓘(ℝ) 𝓘(ℝ) f (Icc x y) t := by
    rw [← f_im] at hγ ⊢
    apply mfderivWithin_comp
    · apply hγ _ (mem_image_of_mem _ ht)
    · rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
      exact h'f _ ht
    · exact subset_preimage_image _ _
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc h _ ht
  rw [this]
  simp only [Function.comp_apply, ContinuousLinearMap.coe_comp']
  have : mfderivWithin 𝓘(ℝ) 𝓘(ℝ) f (Icc x y) t 1
      = derivWithin f (Icc x y) t • (1 : TangentSpace 𝓘(ℝ) (f t)) := by
    simp only [mfderivWithin_eq_fderivWithin, ← fderivWithin_derivWithin, smul_eq_mul, mul_one]
    rfl
  rw [this]
  have : 0 ≤ -derivWithin f (Icc x y) t := by simp [hf.derivWithin_nonpos]
  simp only [map_smul, enorm_smul, f_im, ← Real.enorm_of_nonneg this, enorm_neg]

section

-- variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] {x y : M} {r : ℝ≥0∞} {a b : ℝ}
variable {x y z : M} {r : ℝ≥0∞} {a b : ℝ}

variable (I) in
/-- The Riemannian extended distance between two points, in a manifold where the tangent spaces
have an inner product, defined as the infimum of the lengths of `C^1` paths between the points. -/
noncomputable irreducible_def riemannianEDist (x y : M) : ℝ≥0∞ :=
  ⨅ (γ : Path x y) (_ : ContMDiff (𝓡∂ 1) I 1 γ), ∫⁻ x, ‖mfderiv (𝓡∂ 1) I γ x 1‖ₑ

/-- The Riemannian edistance is bounded above by the length of any `C^1` path from `x` to `y`.
Here, we express this using a path defined on the whole real line, considered on
some interval `[a, b]`. -/
lemma riemannianEDist_le_pathELength {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc a b))
    (ha : γ a = x) (hb : γ b = y) (hab : a ≤ b) :
    riemannianEDist I x y ≤ pathELength I γ a b := by
  let η : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.lineMap a b
  have hη : ContMDiffOn 𝓘(ℝ) I 1 (γ ∘ η) (Icc 0 1) := by
    apply hγ.comp
    · rw [contMDiffOn_iff_contDiffOn]
      exact η.contDiff.contDiffOn
    · rw [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq, ← segment_eq_image_lineMap]
      simp [hab]
  let f : unitInterval → M := fun t ↦ (γ ∘ η) t
  have hf : ContMDiff (𝓡∂ 1) I 1 f := by
    rw [← contMDiffOn_comp_projIcc_iff]
    apply hη.congr (fun t ht ↦ ?_)
    simp only [Function.comp_apply, f, projIcc_of_mem, ht]
  let g : C(unitInterval, M) := ⟨f, hf.continuous⟩
  let g' : Path x y := by
    refine ⟨g, ?_, ?_⟩ <;>
    simp [g, f, η, ContinuousAffineMap.coe_lineMap_eq, ha, hb]
  have A : riemannianEDist I x y ≤ ∫⁻ x, ‖mfderiv (𝓡∂ 1) I g' x 1‖ₑ := by
    rw [riemannianEDist]; exact biInf_le _ hf
  apply A.trans_eq
  rw [lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc]
  have E : pathELength I (g' ∘ projIcc 0 1 zero_le_one) 0 1 = pathELength I (γ ∘ η) 0 1 := by
    apply pathELength_congr (fun t ht ↦ ?_)
    simp only [Function.comp_apply, ht, projIcc_of_mem]
    rfl
  have ha : a = η 0 := by simp [η, ContinuousAffineMap.coe_lineMap_eq]
  have hb : b = η 1 := by simp [η, ContinuousAffineMap.coe_lineMap_eq]
  rw [E, ha, hb]
  apply pathELength_comp_of_monotoneOn zero_le_one _ η.differentiableOn
  · simpa [← ha, ← hb] using hγ.mdifferentiableOn le_rfl
  · apply (AffineMap.lineMap_monotone hab).monotoneOn

omit [∀ (x : M), ENormSMulClass ℝ (TangentSpace I x)] in
/-- If some `r` is strictly larger than the Riemannian edistance between two points, there exists
a path between these two points of length `< r`. Here, we get such a path on `[0, 1]`.
For a more precise version giving locally constant paths around the endpoints, see
`exists_lt_locally_constant_of_riemannianEDist_lt` -/
lemma exists_lt_of_riemannianEDist_lt (hr : riemannianEDist I x y < r) :
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧ ContMDiffOn 𝓘(ℝ) I 1 γ (Icc 0 1) ∧
    pathELength I γ 0 1 < r := by
  simp only [riemannianEDist, iInf_lt_iff, exists_prop] at hr
  rcases hr with ⟨γ, γ_smooth, hγ⟩
  refine ⟨γ ∘ (projIcc 0 1 zero_le_one), by simp, by simp,
    contMDiffOn_comp_projIcc_iff.2 γ_smooth, ?_⟩
  rwa [← lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc]

/-- If some `r` is strictly larger than the Riemannian edistance between two points, there exists
a path between these two points of length `< r`. Here, we get such a path on an arbitrary interval
`[a, b]` with `a < b`, and moreover we ensure that the path is locally constant around `a` and `b`,
which is convenient for gluing purposes. -/
lemma exists_lt_locally_constant_of_riemannianEDist_lt
    (hr : riemannianEDist I x y < r) (hab : a < b) :
    ∃ γ : ℝ → M, γ a = x ∧ γ b = y ∧ ContMDiff 𝓘(ℝ) I 1 γ ∧
    γ =ᶠ[𝓝 a] (fun _ ↦ x) ∧ γ =ᶠ[𝓝 b] (fun _ ↦ y) ∧ pathELength I γ a b < r := by
  /- We start from a path from `x` to `y` defined on `[0, 1]` with short length. Then, we
  reparameterize it using a smooth monotone map `η` from `[a, b]` to `[0, 1]` which is moreover
  locally constant around `a` and `b`.
  Such a map is easy to build with `Real.smoothTransition`. -/
  rcases exists_lt_of_riemannianEDist_lt hr with ⟨γ, hγx, hγy, γ_smooth, hγ⟩
  rcases exists_between hab with ⟨a', haa', ha'b⟩
  rcases exists_between ha'b with ⟨b', ha'b', hb'b⟩
  let η (t : ℝ) : ℝ := Real.smoothTransition ((b' - a') ⁻¹ * (t - a'))
  have A (t) (ht : t < a') : η t = 0 := by
    simp only [η, Real.smoothTransition.zero_iff_nonpos]
    apply mul_nonpos_of_nonneg_of_nonpos
    · simpa using ha'b'.le
    · linarith
  have A' (t) (ht : t < a') : (γ ∘ η) t = x := by simp [A t ht, hγx]
  have B (t) (ht : b' < t) : η t = 1 := by
    simp only [η, Real.smoothTransition.eq_one_iff_one_le, inv_mul_eq_div]
    rw [one_le_div₀] <;> linarith
  have B' (t) (ht : b' < t) : (γ ∘ η) t = y := by simp [B t ht, hγy]
  refine ⟨γ ∘ η, A' _ haa', B' _ hb'b, ?_, ?_, ?_, ?_⟩
  · rw [← contMDiffOn_univ]
    apply γ_smooth.comp
    · rw [contMDiffOn_univ, contMDiff_iff_contDiff]
      fun_prop
    · intro t ht
      exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · filter_upwards [Iio_mem_nhds haa'] with t ht using A' t ht
  · filter_upwards [Ioi_mem_nhds hb'b] with t ht using B' t ht
  · convert hγ using 1
    rw [← A a haa', ← B b hb'b]
    apply pathELength_comp_of_monotoneOn hab.le
    · apply Monotone.monotoneOn
      apply Real.smoothTransition.monotone.comp
      intro t u htu
      dsimp only
      gcongr
      simpa only [inv_nonneg, sub_nonneg] using ha'b'.le
    · simp only [η]
      apply (ContDiff.contDiffOn _).differentiableOn le_rfl
      fun_prop
    · rw [A a haa', B b hb'b]
      apply γ_smooth.mdifferentiableOn le_rfl

lemma riemannianEDist_self : riemannianEDist I x x = 0 := by
  apply le_antisymm _ bot_le
  exact (riemannianEDist_le_pathELength (γ := fun (t : ℝ) ↦ x) (a := 0) (b := 0)
    contMDiffOn_const rfl rfl le_rfl).trans_eq (by simp)

lemma riemannianEDist_comm : riemannianEDist I x y = riemannianEDist I y x := by
  suffices H : ∀ x y, riemannianEDist I y x ≤ riemannianEDist I x y from le_antisymm (H y x) (H x y)
  intro x y
  apply le_of_forall_gt (fun r hr ↦ ?_)
  rcases exists_lt_locally_constant_of_riemannianEDist_lt hr zero_lt_one
    with ⟨γ, γ0, γ1, γ_smooth, -, -, hγ⟩
  let η : ℝ → ℝ := fun t ↦ - t
  have h_smooth : ContMDiff 𝓘(ℝ) I 1 (γ ∘ η) := by
    apply γ_smooth.comp ?_
    simp only [contMDiff_iff_contDiff]
    fun_prop
  have : riemannianEDist I y x ≤ pathELength I (γ ∘ η) (η 1) (η 0) := by
    apply riemannianEDist_le_pathELength h_smooth.contMDiffOn <;> simp [η, γ0, γ1]
  rw [← pathELength_comp_of_antitoneOn zero_le_one] at this; rotate_left
  · exact monotone_id.neg.antitoneOn _
  · exact differentiableOn_neg _
  · exact h_smooth.contMDiffOn.mdifferentiableOn le_rfl
  apply this.trans_lt
  convert hγ
  ext t
  simp [η]

lemma riemannianEDist_triangle :
    riemannianEDist I x z ≤ riemannianEDist I x y + riemannianEDist I y z := by
  apply le_of_forall_gt (fun r hr ↦ ?_)









#exit


end

section

variable [EMetricSpace M] [ChartedSpace H M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

variable (I M) in
/-- Consider a manifold in which the tangent spaces are already endowed with a scalar product, and
already endowed with an extended distance. We say that this is a Riemannian manifold if the distance
is given by the infimum of the lengths of `C^1` paths, measured using the norm in the tangent
spaces.

This is a `Prop` valued typeclass, on top of existing data. -/
class IsRiemannianManifold : Prop where
  out (x y : M) : edist x y = riemannianEDist I x y

/- TODO: show that a vector space with an inner product is a Riemannian manifold. -/

end

section

open Bundle

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

variable (F) in
/-- The standard riemannian metric on a vector space with an inner product, given by this inner
product on each tangent space. -/
noncomputable def riemannianMetricVectorSpace :
    ContMDiffRiemannianMetric 𝓘(ℝ, F) ω F (fun (x : F) ↦ TangentSpace 𝓘(ℝ, F) x) where
  inner x := (innerSL ℝ (E := F) : F →L[ℝ] F →L[ℝ] ℝ)
  symm x v w := real_inner_comm  _ _
  pos x v hv := real_inner_self_pos.2 hv
  isVonNBounded x := by
    change IsVonNBounded ℝ {v : F | ⟪v, v⟫ < 1}
    have : Metric.ball (0 : F) 1 = {v : F | ⟪v, v⟫ < 1} := by
      ext v
      simp only [Metric.mem_ball, dist_zero_right, norm_eq_sqrt_re_inner (𝕜 := ℝ),
        RCLike.re_to_real, Set.mem_setOf_eq]
      conv_lhs => rw [show (1 : ℝ) = √ 1 by simp]
      rw [Real.sqrt_lt_sqrt_iff]
      exact real_inner_self_nonneg
    rw [← this]
    exact NormedSpace.isVonNBounded_ball ℝ F 1
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    convert contMDiffAt_const (c := innerSL ℝ)
    ext v w
    simp? [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
        Trivialization.linearMapAt_apply] says
      simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
        TangentBundle.symmL_model_space, ContinuousLinearMap.coe_comp',
        Trivialization.continuousLinearMapAt_apply, Function.comp_apply,
        Trivialization.linearMapAt_apply, hom_trivializationAt_baseSet,
        TangentBundle.trivializationAt_baseSet, PartialHomeomorph.refl_partialEquiv,
        PartialEquiv.refl_source, PartialHomeomorph.singletonChartedSpace_chartAt_eq,
        Trivial.fiberBundle_trivializationAt', Trivial.trivialization_baseSet, inter_self, mem_univ,
        ↓reduceIte, Trivial.trivialization_apply]
    rfl

noncomputable instance : RiemannianBundle (fun (x : F) ↦ TangentSpace 𝓘(ℝ, F) x) :=
  ⟨(riemannianMetricVectorSpace F).toRiemannianMetric⟩

set_option synthInstance.maxHeartbeats 30000 in
-- otherwise, the instance is not found!
lemma norm_tangentSpace_vectorSpace {x : F} {v : TangentSpace 𝓘(ℝ, F) x} :
    ‖v‖ = ‖show F from v‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]

set_option synthInstance.maxHeartbeats 30000 in
-- otherwise, the instance is not found!
lemma nnnorm_tangentSpace_vectorSpace {x : F} {v : TangentSpace 𝓘(ℝ, F) x} :
    ‖v‖₊ = ‖show F from v‖₊ := by
  simp [nnnorm, norm_tangentSpace_vectorSpace]

lemma enorm_tangentSpace_vectorSpace {x : F} {v : TangentSpace 𝓘(ℝ, F) x} :
    ‖v‖ₑ = ‖show F from v‖ₑ := by
  simp [enorm, nnnorm_tangentSpace_vectorSpace]

open MeasureTheory Measure

lemma lintegral_mfderiv_unitInterval_eq_mfderivWithin_comp_projIcc
    [∀ (y : M), ENorm (TangentSpace I y)] (γ : unitInterval → M) :
    ∫⁻ x, ‖mfderiv (𝓡∂ 1) I γ x 1‖ₑ =
      ∫⁻ x in Icc 0 1, ‖mfderivWithin 𝓘(ℝ) I (γ ∘ (projIcc 0 1 zero_le_one)) (Icc 0 1) x 1‖ₑ := by
  simp_rw [← mfderivWithin_comp_projIcc_one]
  have : MeasurePreserving (Subtype.val : unitInterval → ℝ) volume
    (volume.restrict (Icc 0 1)) := measurePreserving_subtype_coe measurableSet_Icc
  rw [← MeasureTheory.MeasurePreserving.lintegral_comp_emb this
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
  congr
  ext x
  have : x = projIcc 0 1 zero_le_one (x : ℝ) := by simp
  congr

lemma lintegral_mfderiv_unitInterval_eq_mfderiv_comp_projIcc
    [∀ (y : M), ENorm (TangentSpace I y)] (γ : unitInterval → M) :
    ∫⁻ x, ‖mfderiv (𝓡∂ 1) I γ x 1‖ₑ =
      ∫⁻ x in Ioo 0 1, ‖mfderiv 𝓘(ℝ) I (γ ∘ (projIcc 0 1 zero_le_one)) x 1‖ₑ := by
  rw [lintegral_mfderiv_unitInterval_eq_mfderivWithin_comp_projIcc, ← restrict_Ioo_eq_restrict_Icc]
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  congr
  rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]

/-- An inner product vector space is a Riemannian manifold, i.e., the distance between two points
is the infimum of the lengths of paths between these points. -/
instance : IsRiemannianManifold 𝓘(ℝ, F) F := by
  refine ⟨fun x y ↦ le_antisymm ?_ ?_⟩
  · simp only [riemannianEDist, le_iInf_iff]
    intro γ hγ
    let e : ℝ → F := γ ∘ (projIcc 0 1 zero_le_one)
    have D : ContDiffOn ℝ 1 e (Icc 0 1) :=
      contMDiffOn_iff_contDiffOn.mp (hγ.comp_contMDiffOn contMDiffOn_projIcc)
    rw [lintegral_mfderiv_unitInterval_eq_mfderivWithin_comp_projIcc]
    simp only [mfderivWithin_eq_fderivWithin, enorm_tangentSpace_vectorSpace]
    conv_lhs =>
      rw [edist_comm, edist_eq_enorm_sub, show x = e 0 by simp [e], show y = e 1 by simp [e]]
    exact (enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc D zero_le_one).trans_eq rfl
  · let γ := Path.segment x y
    have hγ : ContMDiff (𝓡∂ 1) 𝓘(ℝ, F) 1 γ := by
      rw [← contMDiffOn_comp_projIcc_iff]
      simp only [Path.segment, Path.coe_mk', ContinuousMap.coe_mk, contMDiffOn_iff_contDiffOn, γ]
      have : ContDiff ℝ 1 (AffineMap.lineMap (k := ℝ) x y) := by
        change ContDiff ℝ 1 (ContinuousAffineMap.lineMap (R := ℝ) x y)
        apply ContinuousAffineMap.contDiff
      apply this.contDiffOn.congr (fun t ht ↦ ?_)
      simp [projIcc_of_mem zero_le_one ht]
    have : riemannianEDist 𝓘(ℝ, F) x y ≤ ∫⁻ x, ‖mfderiv (𝓡∂ 1) 𝓘(ℝ, F) γ x 1‖ₑ :=
      (iInf_le _ γ).trans (iInf_le _ hγ)
    apply this.trans_eq
    rw [lintegral_mfderiv_unitInterval_eq_mfderiv_comp_projIcc]
    simp only [mfderivWithin_eq_fderivWithin, enorm_tangentSpace_vectorSpace]
    have : edist x y = ∫⁻ (x_1 : ℝ) in Ioo 0 1, ‖y - x‖ₑ := by
      simp [edist_comm x y, edist_eq_enorm_sub]
    rw [this]
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with z hz
    rw [show y - x = fderiv ℝ (ContinuousAffineMap.lineMap (R := ℝ) x y) z 1 by simp]
    congr
    simp only [Function.comp_apply, mfderiv_eq_fderiv]
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [Ioo_mem_nhds hz.1 hz.2] with w hw
    have : projIcc 0 1 zero_le_one w = w := by rw [projIcc_of_mem _ ⟨hw.1.le, hw.2.le⟩]
    simp only [Function.comp_apply, Path.segment_apply, this, γ]
    rfl

end
