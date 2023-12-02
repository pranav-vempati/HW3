for k in range(78, 100):
    for g in range(100, 200):
        for l in range(200, 300):
            for z in range(300, 400):
                for m in range(400, 500):
                    for t in range(53, 600):
                        for y in range(600, 700):
                            for s in range(500, 600):
                                a[k % g * z//m * s] = a[g//z * m + t - 2 - y]
