import PfaffianDescent.RelativeSurfacePresentation318

/-!
An already chosen exact free presentation remains exact and injective under
the actual coefficient reduction. No new matrix or basis is selected.
-/

noncomputable section
namespace AllCharacteristics
open Module LinearMap Matrix HilbertSurfaceDraft
universe u v w v₀ w₀ t t'

/-- An isomorphism descends through exact coefficient reductions. -/
theorem bijective_reduced_of_exact_reduction_square318
    {S : Type u} [CommRing S] (I : Ideal S)
    {F : Type v} {K : Type w} {F₀ : Type v₀} {K₀ : Type w₀}
    [AddCommGroup F] [AddCommGroup K] [AddCommGroup F₀] [AddCommGroup K₀]
    [Module S F] [Module S K] [Module S F₀] [Module S K₀]
    (f : F →ₗ[S] K) (hf : Function.Bijective f)
    (f₀ : F₀ →ₗ[S] K₀)
    (ρF : F →ₗ[S] F₀) (hρF : Function.Surjective ρF)
    (hkerF : ρF.ker = I • (⊤ : Submodule S F))
    (ρK : K →ₗ[S] K₀) (hρK : Function.Surjective ρK)
    (hkerK : ρK.ker = I • (⊤ : Submodule S K))
    (hcomm : ∀ x, ρK (f x) = f₀ (ρF x)) : Function.Bijective f₀ := by
  have hmap : (I • (⊤ : Submodule S F)).map f =
      I • (⊤ : Submodule S K) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hf.surjective]
  have hzero : ∀ x₀, f₀ x₀ = 0 → x₀ = 0 := by
    intro x₀ hx₀
    obtain ⟨x, hx⟩ := hρF x₀
    have hfx : f x ∈ I • (⊤ : Submodule S K) := by
      rw [← hkerK]
      change ρK (f x) = 0
      rw [hcomm, hx, hx₀]
    obtain ⟨y, hy, hfy⟩ := Submodule.mem_map.mp (hmap.symm ▸ hfx)
    have hyx : y = x := hf.injective hfy
    have hxzero : ρF x = 0 := by
      apply LinearMap.mem_ker.mp
      rw [hkerF, ← hyx]
      exact hy
    exact hx.symm.trans hxzero
  refine ⟨?_, ?_⟩
  · intro x₀ y₀ hxy
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hxy, sub_self]
  · intro k₀
    obtain ⟨k, hk⟩ := hρK k₀
    obtain ⟨x, hx⟩ := hf.surjective k
    exact ⟨ρF x, (hcomm x).symm.trans (by rw [hx, hk])⟩

/-- Matrix multiplication commutes with the actual coordinate reduction. -/
theorem coordinateReduction318_mulVec
    {S : Type u} {A : Type v} {A₀ : Type w} {ι : Type t} {κ : Type t'}
    [CommRing S] [CommRing A] [CommRing A₀] [Algebra S A] [Algebra S A₀]
    [Fintype κ]
    (π : A →ₐ[S] A₀) (M : Matrix ι κ A) (x : κ → A) :
    coordinateReduction318 π (M.mulVecLin x) =
      (M.map π.toRingHom).mulVecLin (coordinateReduction318 π x) := by
  ext i
  change π (∑ j, M i j * x j) = ∑ j, π (M i j) * π (x j)
  simp only [map_sum, map_mul]

/-- Flat base change of a CHOSEN exact free ideal presentation. The theorem
retains its actual mapped matrix, rather than reconstructing a residue basis.
Nilpotence and ambient regularity are unnecessary for this direction. -/
theorem chosen_idealPresentation_reduction_exact318
    {S : Type u} {A : Type v} {A₀ : Type w} {ι : Type t} {κ : Type t'}
    [CommRing S] [CommRing A] [CommRing A₀] [Algebra S A]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Module.Flat S A]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (I : Ideal S)
    (hker : RingHom.ker π = I.map (algebraMap S A))
    (J : Ideal A) [Module.Flat S (A ⧸ J)]
    (a : ι → A) (hJa : J = Ideal.span (Set.range a))
    (M : Matrix ι κ A) (hMinj : Function.Injective M.mulVecLin)
    (hMrange : LinearMap.range M.mulVecLin = LinearMap.ker (rowFunctional008 a)) :
    Function.Injective (M.map π).mulVecLin ∧
      LinearMap.range (M.map π).mulVecLin =
        LinearMap.ker (rowFunctional008 (fun i => π (a i))) := by
  letI : Algebra S A₀ := (π.comp (algebraMap S A)).toAlgebra
  let πS : A →ₐ[S] A₀ := { __ := π, commutes' := fun _ => rfl }
  let J₀ := J.map π
  have ha (i : ι) : a i ∈ J := by
    rw [hJa]
    exact Ideal.mem_span_range_self (x := i)
  have ha₀ (i : ι) : π (a i) ∈ J₀ := Ideal.mem_map_of_mem π (ha i)
  let f := familyIdealMap318 J a ha
  let f₀ := familyIdealMap318 J₀ (fun i => π (a i)) ha₀
  have hf : Function.Surjective f := familyIdealMap318_surjective J a ha hJa
  have hfker : f.ker = LinearMap.ker (rowFunctional008 a) := familyIdealMap318_ker J a ha
  have hf₀ker : f₀.ker = LinearMap.ker (rowFunctional008 (fun i => π (a i))) :=
    familyIdealMap318_ker J₀ (fun i => π (a i)) ha₀
  letI : Module.Flat S J :=
    PfaffianDescent.flat_prescribedIdeal_of_ambient_and_quotient_flat167 J
  let ρF := coordinateReduction318 (ι := ι) πS
  have hρF := coordinateReduction318_surjective (ι := ι) πS hπ
  have hkerF := coordinateReduction318_ker (ι := ι) πS I hker
  have hcomm : ∀ x, actualIdealReduction318 πS J (f x) = f₀ (ρF x) := by
    intro x
    apply Subtype.ext
    change π (∑ i, x i * a i) = ∑ i, π (x i) * π (a i)
    simp only [map_sum, map_mul]
  obtain ⟨ρK', hρKval', hρK', hkerK'⟩ :=
    exists_kernel_reduction_of_exact_square318 I
      (f.restrictScalars S) hf (f₀.restrictScalars S)
      ρF hρF hkerF (actualIdealReduction318 πS J)
      (actualIdealReduction318_ker πS I hker J) hcomm
  let ρK : f.ker →ₗ[S] f₀.ker := ρK'
  have hρKval : ∀ k : f.ker, (ρK k : ι → A₀) = ρF (k : ι → A) := hρKval'
  have hρK : Function.Surjective ρK := hρK'
  have hkerK : ρK.ker = I • (⊤ : Submodule S f.ker) := hkerK'
  let d : (κ → A) →ₗ[A] f.ker := M.mulVecLin.codRestrict f.ker (fun x => by
    rw [hfker, ← hMrange]
    exact LinearMap.mem_range_self _ x)
  have hd : Function.Bijective d := by
    refine ⟨fun x y hxy => hMinj (congrArg Subtype.val hxy), ?_⟩
    intro k
    have hk : (k : ι → A) ∈ LinearMap.range M.mulVecLin := by
      rw [hMrange, ← hfker]
      exact k.property
    obtain ⟨x, hx⟩ := hk
    exact ⟨x, Subtype.ext hx⟩
  have hM₀ker (x₀ : κ → A₀) : (M.map π).mulVecLin x₀ ∈ f₀.ker := by
    obtain ⟨x, rfl⟩ := coordinateReduction318_surjective (ι := κ) πS hπ x₀
    have hx := hρKval (d x)
    have hnat := coordinateReduction318_mulVec πS M x
    have heq : (ρK (d x) : ι → A₀) =
        (M.map π).mulVecLin (coordinateReduction318 πS x) := hx.trans hnat
    rw [← heq]
    exact (ρK (d x)).property
  let d₀ : (κ → A₀) →ₗ[A₀] f₀.ker := (M.map π).mulVecLin.codRestrict f₀.ker hM₀ker
  have hdcomm : ∀ x, ρK (d x) = d₀ (coordinateReduction318 πS x) := by
    intro x
    apply Subtype.ext
    exact (hρKval (d x)).trans (coordinateReduction318_mulVec πS M x)
  have hd₀ : Function.Bijective d₀ :=
    bijective_reduced_of_exact_reduction_square318 I
      (d.restrictScalars S) hd (d₀.restrictScalars S)
      (coordinateReduction318 πS) (coordinateReduction318_surjective πS hπ)
      (coordinateReduction318_ker πS I hker) ρK hρK hkerK hdcomm
  refine ⟨?_, ?_⟩
  · intro x₀ y₀ hxy
    apply hd₀.injective
    exact Subtype.ext hxy
  · rw [← hf₀ker]
    ext x₀
    constructor
    · rintro ⟨y₀, rfl⟩
      exact (d₀ y₀).property
    · intro hx₀
      obtain ⟨y₀, hy₀⟩ := hd₀.surjective ⟨x₀, hx₀⟩
      exact ⟨y₀, congrArg Subtype.val hy₀⟩

end AllCharacteristics
end
