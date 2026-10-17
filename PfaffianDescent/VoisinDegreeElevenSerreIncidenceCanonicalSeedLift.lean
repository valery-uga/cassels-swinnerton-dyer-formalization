import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSeedFactor

/-! # Actual original marked supports lift into the actual canonical incidence -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceCanonicalSupport_zeroLift
    {S B X P Z T D : Scheme.{u}}
    (b : B ⟶ S) (x : X ⟶ S) (p : P ⟶ S)
    (marked : Fin 3 → (B ⟶ X)) (hm : ∀ i, marked i ≫ x = b)
    (zero : Z ⟶ pullback x p) (t : S ⟶ P) (d : D ⟶ S) (i : D ⟶ X)
    (v : D ≅ pullback (zero ≫ pullback.snd x p) t)
    (hv : v.hom ≫ pullback.snd (zero ≫ pullback.snd x p) t = d)
    (hvs : v.hom ≫ pullback.fst (zero ≫ pullback.snd x p) t ≫
      zero ≫ pullback.fst x p = i)
    (a : T ⟶ pullback b p) (r : T ⟶ S)
    (ha : a ≫ pullback.snd b p = r ≫ t)
    (δ : T ⟶ D) (hδd : δ ≫ d = r)
    (j : Fin 3) (hδi : δ ≫ i = a ≫ pullback.fst b p ≫ marked j) :
    (δ ≫ v.hom ≫ pullback.fst (zero ≫ pullback.snd x p) t) ≫ zero =
      a ≫ fixedLinearSystemIncidenceMap b x p marked hm j := by
  apply pullback.hom_ext
  · simp only [Category.assoc, fixedLinearSystemIncidenceMap_fst]
    exact (congrArg (fun q => δ ≫ q) hvs).trans hδi
  · calc
      _ = δ ≫ v.hom ≫ (pullback.fst (zero ≫ pullback.snd x p) t ≫
          (zero ≫ pullback.snd x p)) := by simp only [Category.assoc]
      _ = δ ≫ v.hom ≫ (pullback.snd (zero ≫ pullback.snd x p) t ≫ t) :=
        congrArg (fun q => δ ≫ v.hom ≫ q) pullback.condition
      _ = (δ ≫ (v.hom ≫ pullback.snd (zero ≫ pullback.snd x p) t)) ≫ t := by
        simp only [Category.assoc]
      _ = (δ ≫ d) ≫ t := by rw [hv]
      _ = r ≫ t := by rw [hδd]
      _ = a ≫ pullback.snd b p := ha.symm
      _ = _ := by rw [Category.assoc, fixedLinearSystemIncidenceMap_snd]

theorem serreIncidenceCanonicalSupport_exists_seed
    {S B X P Z T D : Scheme.{u}}
    (b : B ⟶ S) (x : X ⟶ S) (p : P ⟶ S)
    (marked : Fin 3 → (B ⟶ X)) (hm : ∀ i, marked i ≫ x = b)
    (zero : Z ⟶ pullback x p) [IsClosedImmersion zero]
    (t : S ⟶ P) (d : D ⟶ S) (i : D ⟶ X)
    (v : D ≅ pullback (zero ≫ pullback.snd x p) t)
    (hv : v.hom ≫ pullback.snd (zero ≫ pullback.snd x p) t = d)
    (hvs : v.hom ≫ pullback.fst (zero ≫ pullback.snd x p) t ≫
      zero ≫ pullback.fst x p = i)
    (a : T ⟶ pullback b p) (r : T ⟶ S)
    (ha : a ≫ pullback.snd b p = r ≫ t)
    (δ : Fin 3 → (T ⟶ D)) (hδd : ∀ j, δ j ≫ d = r)
    (hδi : ∀ j, δ j ≫ i = a ≫ pullback.fst b p ≫ marked j) :
    ∃ s : T ⟶ serreThreePointSectionIncidence b x p marked hm zero,
      s ≫ serreThreePointSectionIncidenceToParameters b x p marked hm zero = r ≫ t ∧
      s ≫ serreThreePointSectionIncidenceToConfiguration b x p marked hm zero =
        a ≫ pullback.fst b p := by
  let l := fun j => δ j ≫ v.hom ≫ pullback.fst (zero ≫ pullback.snd x p) t
  have hl : ∀ j, l j ≫ zero = a ≫ fixedLinearSystemIncidenceMap b x p marked hm j := by
    intro j
    exact serreIncidenceCanonicalSupport_zeroLift b x p marked hm zero t d i v hv hvs
      a r ha (δ j) (hδd j) j (hδi j)
  refine ⟨serreIncidenceSeed b x p marked hm zero a l hl, ?_, ?_⟩
  · exact (serreIncidenceSeed_toParameters b x p marked hm zero a l hl).trans ha
  · exact serreIncidenceSeed_toConfiguration b x p marked hm zero a l hl

end PfaffianDescent
