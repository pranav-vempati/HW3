for i in range(0, 128):
    for j in range(27, 300):
        for k in range(j, 400):
            for g in range(5, 800):
                a[i % j + k * g - 1] = a[i * 2 % g - 20]
