#!/bin/bash
# coding=utf-8

import subprocess
import time
import linecache
import re
import signal

def get_std_output(k:int, input_file_name:str, output_file_name:str):
    with open(input_file_name, 'r') as infile, open(output_file_name, 'w') as outfile:
        command = 'datacheck_win -i ' + input_file_name
        popen = subprocess.Popen(command, shell=True, stdin=subprocess.PIPE,
                                stdout=outfile.fileno(), stderr=subprocess.STDOUT)
    
        popen.stdin.flush()
        popen.communicate()
        

def get_java_output(command:str, input_file_name:str, output_file_name:str):
    with open(input_file_name, 'r') as infile, open(output_file_name, 'w') as outfile:
        popen = subprocess.Popen(command, shell=True, stdin=subprocess.PIPE,
                               stdout=outfile.fileno(), stderr=subprocess.STDOUT)
        start_time = time.time()

        for line in infile:
            request = line
            # resolve the time to cast data
            cast_time = re.findall(r"\[(.+)\]", request)
            cast_time = float(cast_time[0])   
            # get standard request
            request = request.replace('[' + str(cast_time) + ']', "") 

            # sleep until the specific time
            current_time = time.time() - start_time
            sleep_time = cast_time - current_time
            time.sleep(abs(sleep_time))

            # debug information
            print( "current_time is " + str(round( (time.time() - start_time), 4)) )
            print(line, end='')

            # cast data to stdin 
            popen.stdin.write(bytes(request, 'utf-8'))
            popen.stdin.flush()
        
        popen.communicate()

        print('')
        print(round(time.time() - start_time, 4))
        print('You\'ve got output successfully!')

def main():
    get_java_output("java -jar homework7-SS-Elevators.jar", "sample0.txt", "my_output_0.txt")

if __name__ == '__main__':
    main()