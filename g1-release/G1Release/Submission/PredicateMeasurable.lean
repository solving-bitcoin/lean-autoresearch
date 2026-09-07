import G1Release.Submission.GameViews

namespace G1Release.Submission.PredicateMeasurable
open MeasureTheory

theorem event {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    [Countable A] [Countable B] [DiscreteMeasurableSpace A] [DiscreteMeasurableSpace B]
    (predicate : A → B → Prop) (left : Ω → A) (right : Ω → B)
    (hl : Measurable left) (hr : Measurable right) :
    MeasurableSet {ω | predicate (left ω) (right ω)} :=
  (hl.prodMk hr) (MeasurableSet.of_discrete : MeasurableSet {p : A × B | predicate p.1 p.2})

end G1Release.Submission.PredicateMeasurable
