from get_output import get_java_output

command = "java -jar SS-Elevators-V1.jar"

def autotest(sample_num:int):
    for k in range(sample_num):
        input = 'sample' + str(k) + '.txt'
        # get standard output
        # output = 'standard_output_' + str(k) + '.txt'
        # get_std_output(k, input, output)
        # get players output
        output = 'my_output_' + str(k) + '.txt'
        get_java_output(command, input, output)


def main():
    autotest(3)

if __name__ == '__main__':
    main()