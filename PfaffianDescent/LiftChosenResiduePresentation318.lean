import PfaffianDescent.RelativeSurfacePresentation318

/-!
Lift an arbitrary exact residue presentation to a relative free ideal
presentation. In the semilocal surface application the residue presentation
is supplied by the semilocal Hilbert--Burch construction. This lifting
argument itself has no residue-locality or domain hypothesis.
-/

noncomputable section
namespace AllCharacteristics
open Module LinearMap Matrix HilbertSurfaceDraft
universe u v w

theorem exists_actual_relative_presentation_lifting_residue318
    {S : Type u} {A : Type v} {A₀ : Type w}
    [CommRing S] [CommRing A] [CommRing A₀] [Algebra S A] [Algebra S A₀]
    [Module.Flat S A]
    (π : A →ₐ[S] A₀) (hπ : Function.Surjective π)
    (I : Ideal S) (hI : IsNilpotent I)
    (hker : RingHom.ker π.toRingHom = I.map (algebraMap S A))
    (J : Ideal A) [Module.Flat S (A ⧸ J)] {m : ℕ}
    (M₀ : Matrix (Option (Fin m)) (Fin m) A₀) (a₀ : Option (Fin m) → A₀)
    (hJ₀ : J.map π.toRingHom = Ideal.span (Set.range a₀))
    (hM₀inj : Function.Injective M₀.mulVecLin)
    (hM₀range : LinearMap.range M₀.mulVecLin = LinearMap.ker (rowFunctional008 a₀)) :
    ∃ (M : Matrix (Option (Fin m)) (Fin m) A) (a : Option (Fin m) → A),
      M.map π.toRingHom = M₀ ∧
      (∀ i, π (a i) = a₀ i) ∧
      J = Ideal.span (Set.range a) ∧
      Function.Injective M.mulVecLin ∧
      LinearMap.range M.mulVecLin = LinearMap.ker (rowFunctional008 a) := by
  let J₀ := J.map π.toRingHom
  obtain ⟨a, ha, haπ, hJa⟩ :=
    exists_prescribedIdeal_family_lifts_of_nilpotent_reduction318
      π.toRingHom hπ I hI hker J a₀ hJ₀
  let f := familyIdealMap318 J a ha
  have hf : Function.Surjective f := familyIdealMap318_surjective J a ha hJa
  have ha₀ (i : Option (Fin m)) : a₀ i ∈ J₀ := by
    change a₀ i ∈ J.map π.toRingHom
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
  exact ⟨M, a, hMmap, haπ, hJa, hMinj,
    hMrange.trans (familyIdealMap318_ker J a ha)⟩

end AllCharacteristics
end
