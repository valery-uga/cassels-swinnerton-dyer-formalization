import PfaffianDescent.ActualSyzygyBasisLift318
import PfaffianDescent.HilbertBurchExistence318

/-!
Construct an actual relative free presentation from ambient/quotient flatness
and regularity of the actual residue ring. No relative presentation is input.
The matrix is lifted inside the kernel of the chosen original ideal map.
-/

noncomputable section
namespace AllCharacteristics
open Module LinearMap Matrix HilbertSurfaceDraft
universe u v w t

def familyIdealMap318
    {A : Type v} {ι : Type t} [CommRing A] [Fintype ι]
    (J : Ideal A) (a : ι → A) (ha : ∀ i, a i ∈ J) : (ι → A) →ₗ[A] J :=
  (Fintype.linearCombination A a).codRestrict J (fun x => by
    change (∑ i, x i • a i) ∈ J
    exact J.sum_mem (fun i _ => J.smul_mem (x i) (ha i)))

theorem familyIdealMap318_surjective
    {A : Type v} {ι : Type t} [CommRing A] [Fintype ι]
    (J : Ideal A) (a : ι → A) (ha : ∀ i, a i ∈ J)
    (hspan : J = Ideal.span (Set.range a)) :
    Function.Surjective (familyIdealMap318 J a ha) := by
  intro j
  have hj : (j : A) ∈ LinearMap.range (Fintype.linearCombination A a) := by
    rw [Fintype.range_linearCombination]
    change (j : A) ∈ Ideal.span (Set.range a)
    rw [← hspan]
    exact j.property
  obtain ⟨x, hx⟩ := hj
  exact ⟨x, Subtype.ext hx⟩

theorem familyIdealMap318_ker
    {A : Type v} {ι : Type t} [CommRing A] [Fintype ι]
    (J : Ideal A) (a : ι → A) (ha : ∀ i, a i ∈ J) :
    (familyIdealMap318 J a ha).ker = (rowFunctional008 a).ker := by
  have hrow : J.subtype.comp (familyIdealMap318 J a ha) = rowFunctional008 a := by
    ext x
    change (∑ i, x i * a i) = ∑ i, a i * x i
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [← hrow, LinearMap.ker_comp, Submodule.ker_subtype]
  rfl

/-- Every original flat embedded deformation on a residue regular surface
has an actual length-one free ideal resolution. Both generator lifts and
syzygy lifts are chosen inside the original ideal and its actual kernel.
The resulting matrix reduces entrywise to an actual residue HB matrix. -/
theorem exists_actual_relative_surface_presentation318
    {S : Type u} {A : Type v} {A₀ : Type w}
    [CommRing S] [CommRing A] [CommRing A₀] [Algebra S A] [Algebra S A₀]
    [Module.Flat S A] [IsRegularLocalRing A₀]
    (π : A →ₐ[S] A₀) (hπ : Function.Surjective π)
    (I : Ideal S) (hI : IsNilpotent I)
    (hker : RingHom.ker π.toRingHom = I.map (algebraMap S A))
    (hdim : ringKrullDim A₀ = 2) (J : Ideal A)
    [Module.Flat S (A ⧸ J)] [IsArtinianRing (A₀ ⧸ J.map π.toRingHom)] :
    ∃ (m : ℕ) (M₀ : Matrix (Option (Fin m)) (Fin m) A₀)
      (M : Matrix (Option (Fin m)) (Fin m) A)
      (a : Option (Fin m) → A),
      M.map π.toRingHom = M₀ ∧
      (∀ i, π (a i) = PfaffianDescent.hilbertBurchCofactors318 M₀ i) ∧
      J = Ideal.span (Set.range a) ∧
      Function.Injective M.mulVecLin ∧
      LinearMap.range M.mulVecLin = LinearMap.ker (rowFunctional008 a) := by
  let J₀ := J.map π.toRingHom
  obtain ⟨m, M₀, hM₀inj, hJ₀, hM₀range⟩ :=
    HilbertSurfaceDraft.exists_hilbertBurch_presentation_regularLocal_surface011 hdim J₀
  let a₀ := PfaffianDescent.hilbertBurchCofactors318 M₀
  obtain ⟨a, ha, haπ, hJa⟩ :=
    exists_prescribedIdeal_family_lifts_of_nilpotent_reduction318
      π.toRingHom hπ I hI hker J a₀ hJ₀
  let f := familyIdealMap318 J a ha
  have hf : Function.Surjective f := familyIdealMap318_surjective J a ha hJa
  have ha₀ (i : Option (Fin m)) : a₀ i ∈ J₀ := by
    rw [hJ₀]
    exact Ideal.mem_span_range_self (x := i)
  let f₀ := familyIdealMap318 J₀ a₀ ha₀
  have hf₀ker : f₀.ker = (rowFunctional008 a₀).ker :=
    familyIdealMap318_ker J₀ a₀ ha₀
  let d₀ : (Fin m → A₀) →ₗ[A₀] f₀.ker :=
    M₀.mulVecLin.codRestrict f₀.ker (fun x => by
      rw [hf₀ker, ← hM₀range]
      exact LinearMap.mem_range_self _ x)
  have hd₀inj : Function.Injective d₀ := by
    intro x y hxy
    exact hM₀inj (congrArg Subtype.val hxy)
  have hd₀surj : Function.Surjective d₀ := by
    intro k₀
    have hk₀ : (k₀ : Option (Fin m) → A₀) ∈ LinearMap.range M₀.mulVecLin := by
      rw [hM₀range, ← hf₀ker]
      exact k₀.property
    obtain ⟨x, hx⟩ := hk₀
    exact ⟨x, Subtype.ext hx⟩
  let e₀ := LinearEquiv.ofBijective d₀ ⟨hd₀inj, hd₀surj⟩
  let b₀ : Basis (Fin m) A₀ f₀.ker := (Pi.basisFun A₀ (Fin m)).map e₀
  have hb₀ (j : Fin m) (i : Option (Fin m)) :
      (b₀ j : Option (Fin m) → A₀) i = M₀ i j := by
    simp only [b₀, Basis.map_apply, Pi.basisFun_apply, e₀,
      LinearEquiv.ofBijective_apply]
    change (M₀ *ᵥ Pi.single j 1) i = M₀ i j
    rw [Matrix.mulVec_single_one]
    rfl
  letI : Module.Flat S J :=
    PfaffianDescent.flat_prescribedIdeal_of_ambient_and_quotient_flat167 J
  have hcomm : ∀ x, actualIdealReduction318 π J (f x) =
      f₀ (coordinateReduction318 π x) := by
    intro x
    apply Subtype.ext
    change π (∑ i, x i * a i) = ∑ i, π (x i) * a₀ i
    have haπ' : ∀ i, π (a i) = a₀ i := haπ
    simp only [map_sum, map_mul, haπ']
  obtain ⟨b, hb⟩ := exists_actual_relative_syzygyBasis318 π hπ I hI hker f hf f₀
    (actualIdealReduction318 π J) (actualIdealReduction318_ker π I hker J) hcomm b₀
  let g : (Fin m → A) →ₗ[A] (Option (Fin m) → A) :=
    f.ker.subtype.comp b.equivFun.symm.toLinearMap
  let M : Matrix (Option (Fin m)) (Fin m) A := fun i j => (b j : Option (Fin m) → A) i
  have hM : M.mulVecLin = g := by
    apply (Pi.basisFun A (Fin m)).ext
    intro j
    ext i
    simp only [Pi.basisFun_apply]
    change (M *ᵥ Pi.single j 1) i =
      (b.equivFun.symm (Pi.single j 1) : Option (Fin m) → A) i
    rw [Matrix.mulVec_single_one]
    have hsingle : b.equivFun.symm (Pi.single j 1) = b j := by
      rw [Basis.equivFun_symm_apply]
      simp
    rw [hsingle]
    rfl
  have hMmap : M.map π.toRingHom = M₀ := by
    ext i j
    exact (hb j i).trans (hb₀ j i)
  have hMinj : Function.Injective M.mulVecLin := by
    rw [hM]
    exact f.ker.subtype_injective.comp b.equivFun.symm.injective
  have hMrange : LinearMap.range M.mulVecLin = f.ker := by
    rw [hM]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (b.equivFun.symm y).property
    · intro hx
      refine ⟨b.equivFun ⟨x, hx⟩, ?_⟩
      change (b.equivFun.symm (b.equivFun ⟨x, hx⟩) : Option (Fin m) → A) = x
      rw [b.equivFun.symm_apply_apply]
  exact ⟨m, M₀, M, a, hMmap, haπ, hJa, hMinj,
    hMrange.trans (familyIdealMap318_ker J a ha)⟩

end AllCharacteristics
end
