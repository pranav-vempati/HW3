from skeleton import analyze_file

# fill these in with the expected result for each test
tests = {"0.py" : (False, True),
         "1.py" : (False, False),
         "2.py" : (True, True),
         "3.py" : (True, False),
         "4.py" : (True, True),
         "5.py" : (True, False),
         "6.py" : (True, True),
         "7.py" : (True, True),
         "pvempati_0.py" : (True, False),
         "pvempati_1.py" : (False, True),
         "pvempati_2.py" : (False, False),
         "tbanghar_3.py": (True, True),
         "tbanghar_4.py": (True, True),
         "tbanghar_5.py": (True, False),
         "pvempati_6.py": (False, False)
}

passed = 0
failed = 0
for t in tests:
    result = tests[t]
    test_file = "test_cases/" + t
    print("running: " + test_file)
    print("")
    res = analyze_file(test_file)
    if res != result:
        print("failed test: " + t)
        failed += 1
    else:
        passed += 1

print("passed: " + str(passed))
print("failed: " + str(failed))
    
