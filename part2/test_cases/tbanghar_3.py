for i in range(0, 128):
    for j in range(27, 300):
        for k in range(j, 400):
            a[i * j + k - 1] = a[i*2]
