#!/bin/bash
# coding=utf-8

import os
import random

MAX_TBASE = 70
min_time_span = 0.0
max_time_span = 10.0
min_floor = -3
max_floor = 20

file_num = 100        # num of sample files to be generated
request_num = 30    # num of request per sample

def sample_generator(n: int, filename: str):
    with open(filename, 'w') as f:
        base_time = random.uniform(0.0, 5.0)
        for i in range(n):
            # random time
            time_span = random.uniform(min_time_span, max_time_span)
            base_time = base_time + time_span

            if base_time > MAX_TBASE:
                break
            # random floor
            from_floor = 0
            while from_floor == 0:
                from_floor = random.randint(min_floor, max_floor)
            to_floor = 0
            while to_floor == 0 or from_floor == to_floor:
                to_floor = random.randint(min_floor, max_floor)
            # random request
            f.write("[" + str(round(base_time, 1)) + "]" + 
                    str(i) + "-FROM-" + str(from_floor) + "-TO-" + str(to_floor) + "\n")

def dirs_generator():
    os.mkdir("sample_data_set")
    os.chdir("./sample_data_set/")
    n = request_num 
    for i in range(file_num):
        filename = "sample" + str(i) + ".txt"
        sample_generator(n, filename)

def main():
    dirs_generator()

if __name__ == '__main__':
    main()

            