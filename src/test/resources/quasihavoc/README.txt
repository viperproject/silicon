Here is a directory of all the havoc tests

Havoc: basic havoc tests on fields
    1. Disjoint references are not modified
    2. Havoc one field. Its value changes
    6. Havoc with fractions
    7. Similar example as 6, but doesn't verify
    8. Two fractional permissions can alias, but
        we don't know until after we've havocked
    9. Variant of 8 that fails

Havoc_impl: havoc tests where we have an implication
    1. Basic havoc tests with implications that succeed
    2. Testing with trivial true/false conditions
    3. Havocked field in the condition
    4. Disallow multiple implications in parser
    5. Allow multiple implications if grouped by parens

Pred: Testing havoc with predicates
    1. Predicate snapshot is replaced, but we still know
        that the predicate conditions hold
    2. Fractional predicates
    3. Checking if predicate args are equal
    4. Predicates with implications
    5. Conditional havoc where we learn the condition later

Wand:
    1. Simple example where havocking changes the value
    2. Example with a list
    3. Surprising case which makes sense
    4. Wands with conditionals and predicates
    5. Similar to 4
    6. Magic wand with disjunction (nothing special)

Havoc_qp:
    1. Test basic qp funcionality
    2. basic qp with havoc that fails
    3. qp with conditional havoc
    4. qp with predicates
    5. more complicated qp predicates
    6. qp testing injectivity

havocall:
    1. a separate list remains unhavocked
    2. basic failure
    3. one specific value changes
    4. distinct value does not change
    5. havocall with vacuous condition
    6. havocall with predicates
    7. havocall with predicates and injectivity check
    8. 7 but checking for a specific element
    9. havocall without qp
    10. havocall with a magic wand
    11. havocall injectivity check
    12. havocall with no condition
    13. havocall no condition qp
