import PfaffianDescent.ExactReductionSquare318
import PfaffianDescent.FlatPrescribedIdealFamilyGeneration318
import Mathlib.LinearAlgebra.Pi

/-!
Actual whole-ideal reduction, with kernel computed from flatness of A/J.
-/

noncomputable section
namespace AllCharacteristics
open LinearMap
universe u v w t

def coordinateReduction318
    {S : Type u} {A : Type v} {A₀ : Type w} {ι : Type t}
    [CommRing S] [CommRing A] [CommRing A₀] [Algebra S A] [Algebra S A₀]
    (π : A →ₐ[S] A₀) : (ι → A) →ₗ[S] (ι → A₀) :=
  LinearMap.pi (fun i => π.toLinearMap.comp (LinearMap.proj i))

@[simp] theorem coordinateReduction318_apply
    {S : Type u} {A : Type v} {A₀ : Type w} {ι : Type t}
    [CommRing S] [CommRing A] [CommRing A₀] [Algebra S A] [Algebra S A₀]
    (π : A →ₐ[S] A₀) (x : ι → A) (i : ι) :
    coordinateReduction318 π x i = π (x i) := rfl

theorem coordinateReduction318_surjective
    {S : Type u} {A : Type v} {A₀ : Type w} {ι : Type t}
    [CommRing S] [CommRing A] [CommRing A₀] [Algebra S A] [Algebra S A₀]
    (π : A →ₐ[S] A₀) (hπ : Function.Surjective π) :
    Function.Surjective (coordinateReduction318 (ι := ι) π) := by
  intro x₀
  choose x hx using fun i => hπ (x₀ i)
  exact ⟨x, funext hx⟩

/-- Reduction of a finite free module has exactly the expected kernel;
the reverse inclusion uses the finite coordinate decomposition explicitly. -/
theorem coordinateReduction318_ker
    {S : Type u} {A : Type v} {A₀ : Type w} {ι : Type t}
    [CommRing S] [CommRing A] [CommRing A₀] [Algebra S A] [Algebra S A₀]
    [Fintype ι] [DecidableEq ι]
    (π : A →ₐ[S] A₀) (I : Ideal S)
    (hker : RingHom.ker π.toRingHom = I.map (algebraMap S A)) :
    (coordinateReduction318 (ι := ι) π).ker =
      I • (⊤ : Submodule S (ι → A)) := by
  have hA : π.toLinearMap.ker = I • (⊤ : Submodule S A) := by
    ext x
    rw [Ideal.smul_top_eq_map]
    exact show π x = 0 ↔ x ∈ I.map (algebraMap S A) by rw [← hker]; rfl
  apply le_antisymm
  · intro x hx
    have hcoord (i : ι) : x i ∈ I • (⊤ : Submodule S A) := by
      rw [← hA]
      exact congrFun hx i
    have hsingle (i : ι) : Pi.single i (x i) ∈ I • (⊤ : Submodule S (ι → A)) := by
      have hm : Pi.single i (x i) ∈
          (I • (⊤ : Submodule S A)).map (LinearMap.single S (fun _ : ι => A) i) :=
        Submodule.mem_map.mpr ⟨x i, hcoord i, rfl⟩
      rw [Submodule.map_smul''] at hm
      exact (smul_mono_right I (show (⊤ : Submodule S A).map
        (LinearMap.single S (fun _ : ι => A) i) ≤ ⊤ from le_top)) hm
    have hsum : (∑ i, Pi.single i (x i)) = x := by
      ext i
      simp
    rw [← hsum]
    exact Submodule.sum_mem _ (fun i _ => hsingle i)
  · apply Submodule.smul_le.mpr
    intro s hs x _
    change coordinateReduction318 π (s • x) = 0
    ext i
    change π (s • x i) = 0
    rw [map_smul]
    have hz : algebraMap S A₀ s = 0 := by
      rw [← π.commutes]
      change algebraMap S A s ∈ RingHom.ker π.toRingHom
      rw [hker]
      exact Ideal.mem_map_of_mem (algebraMap S A) hs
    rw [Algebra.smul_def, hz, zero_mul]

def actualIdealReduction318
    {S : Type u} {A : Type v} {A₀ : Type w}
    [CommRing S] [CommRing A] [CommRing A₀] [Algebra S A] [Algebra S A₀]
    (π : A →ₐ[S] A₀) (J : Ideal A) :
    J →ₗ[S] J.map π.toRingHom where
  toFun j := ⟨π (j : A), Ideal.mem_map_of_mem _ j.property⟩
  map_add' _ _ := Subtype.ext (map_add π _ _)
  map_smul' s j := Subtype.ext (π.toLinearMap.map_smul s (j : A))

@[simp] theorem actualIdealReduction318_apply
    {S : Type u} {A : Type v} {A₀ : Type w}
    [CommRing S] [CommRing A] [CommRing A₀] [Algebra S A] [Algebra S A₀]
    (π : A →ₐ[S] A₀) (J : Ideal A) (j : J) :
    (actualIdealReduction318 π J j : A₀) = π (j : A) := rfl

theorem actualIdealReduction318_surjective
    {S : Type u} {A : Type v} {A₀ : Type w}
    [CommRing S] [CommRing A] [CommRing A₀] [Algebra S A] [Algebra S A₀]
    (π : A →ₐ[S] A₀) (hπ : Function.Surjective π) (J : Ideal A) :
    Function.Surjective (actualIdealReduction318 π J) := by
  intro j₀
  obtain ⟨j, hj, hj₀⟩ :=
    (Ideal.mem_map_iff_of_surjective π.toRingHom hπ).mp j₀.property
  exact ⟨⟨j, hj⟩, Subtype.ext hj₀⟩

/-- This comparison uses flatness of the original quotient. Its kernel
identity is not supplied as presentation data. -/
theorem actualIdealReduction318_ker
    {S : Type u} {A : Type v} {A₀ : Type w}
    [CommRing S] [CommRing A] [CommRing A₀] [Algebra S A] [Algebra S A₀]
    (π : A →ₐ[S] A₀) (I : Ideal S)
    (hker : RingHom.ker π.toRingHom = I.map (algebraMap S A))
    (J : Ideal A) [Module.Flat S (A ⧸ J)] :
    (actualIdealReduction318 π J).ker = I • (⊤ : Submodule S J) := by
  let q := (Ideal.Quotient.mkₐ S J).toLinearMap
  have hqker : q.ker = J.restrictScalars S := by
    ext x
    exact Ideal.Quotient.eq_zero_iff_mem
  have hinter := LinearMap.ker_inf_smul_top_eq_smul_of_flat I q
    Ideal.Quotient.mk_surjective
  have hmem (j : J) : j ∈ I • (⊤ : Submodule S J) ↔
      (j : A) ∈ I • J.restrictScalars S :=
    Submodule.mem_smul_top_iff I (J.restrictScalars S) j
  ext j
  rw [hmem]
  change actualIdealReduction318 π J j = 0 ↔ (j : A) ∈ I • J.restrictScalars S
  rw [← hqker, ← hinter]
  constructor
  · intro hj
    refine ⟨?_, ?_⟩
    · rw [hqker]; exact j.property
    · rw [Ideal.smul_top_eq_map, ← hker]
      exact congrArg Subtype.val hj
  · rintro ⟨_, hj⟩
    apply Subtype.ext
    change π (j : A) = 0
    rwa [Ideal.smul_top_eq_map, ← hker] at hj

end AllCharacteristics
end
