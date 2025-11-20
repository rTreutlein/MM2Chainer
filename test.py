from mork_handler import MorkHandler

# Define a couple of small KB/query pairs to exercise the chainer.
tests = [
    {
        "name": "Wake up early every day",
        "kb": [
            '(: Early (-> Type Type))',
            '(: WakeUp (-> Concept Concept Type))',
            '(: Day (-> Concept Type))',
            '(: Person (-> Concept Type))',
            '(: Speaker (-> Concept Type))',
            '(: speaker_implies_person (Implication (Speaker $x) (Person $x)) (STV 0.9 0.9))',
            '(: i_wake_up_early_every_day (Implication (Day $d) (And (WakeUp i_speaker $d) (Early (WakeUp i_speaker $d)))) (STV 0.9 0.9))',
            '(: i_speaker_is_speaker (Speaker i_speaker) (STV 0.9 0.9))',
        ],
        "queries": [
            {
                "question": "Who wakes up early every day?",
                "query": '(: $prf (Implication (Day $d) (And (WakeUp $who $d) (Early (WakeUp $who $d)))) $tv)',
            }
        ],
    },
    {
        "name": "Bob plays tennis",
        "kb": [
            "(: bob_name (Name bob_obj Bob) (STV 1.0 1.0))",
            "(: tennis (Name tennis_obj Tennis) (STV 1.0 1.0))",
            "(: bob_play_tennis (Play bob_obj tennis_obj) (STV 0.1 0.6))",
        ],
        "queries": [
            {
                "question": "What is the probability that Bob is playing tennis now?",
                "query": "(: $prf (And (Name $bob_obj Bob) (Name $tennis_obj Tennis) (Play $bob_obj $tennis_obj)) $tv)",
            }
        ],
    },
    {
        "name": "What kind of thing is a camera?",
        "kb": [
            '(: camera_is_device_that_takes_pictures (Implication (Camera $camera) (And (Device $camera) (Take $take_event) (Agent $take_event $camera) (Picture $picture) (Photograph $picture) (Patient $take_event $picture))) (STV 0.9 0.9))',
            '(: cameras_are_things (Implication (Camera $x_camera_1) (Thing $x_camera_1)) (STV 0.9 0.9))',
            '(: camera_1_is_camera (Camera camera_1) (STV 0.9 0.9))',
        ],
        "queries": [
            {
                "question": "What kind of thing is a camera?",
                "query": "(: $prf_what_kind_of_thing_is_camera (And (Camera $x_camera_q1) (Thing $x_camera_q1)) $tv_what_kind_of_thing_is_camera)",
            }
        ],
    },
    {
        "name": "Nested Implication",
        "kb": [
                '(: a_b (Implication A B) (STV 1.0 1.0))',
                '(: a_b_c (Implication (Implication A B) C) (STV 1.0 1.0))',
        ],
        "queries": [
                {
                    "question": "Nested Implication",
                    "query": '(: $prf C $tv)',
                },
        ],
    },
    {
        "name": "What was Bob doing yesterday?",
        "kb": [
          "(: bob_name (Name bob_obj \"Bob\") (STV 1.0 1.0))",
          "(: bob_swimming (AtTime (Swimming bob_obj) date_obj) (STV 1.0 1.0))",
          "(: swimming_to_doing (Implication (Swimming $x) (And (Name $swimming_obj \"Swimming\") (Doing $x $swimming_obj))) (STV 1.0 1.0))",
          "(: at_time_transfer (Implication (And (AtTime $what $when) (Implication $what $else)) (AtTime $else $when)) (STV 1.0 1.0))"
        ],
        "queries": [
          {
            "question": "11.10.2025, What was Bob doing yesterday?",
            "query": "(: $prf (And (Name bob_obj \"Bob\") (AtTime (And (Name $what $what_name) (Doing bob_obj $what)) date_obj) ) (STV 1.0 1.0))",
          },
        ],
    },
]


def run_test(test_def: dict,log=True) -> None:
    print(f"\n=== {test_def['name']} ===")
    handler = MorkHandler()

    for atom in test_def["kb"]:
        print("... adding to space: " + atom)
        handler.add_atom(atom,log=log)

    for q in test_def["queries"]:
        question = q.get("question")
        query = q["query"]
        if question:
            print(question)
        print("... chaining for: " + query)
        result = handler.query(query,log=log)
        print("\n--- Result ---")
        for line in result:
            print(line)

if __name__ == "__main__":
    #    for test in tests:
    #       run_test(test)
    run_test(tests[4])
