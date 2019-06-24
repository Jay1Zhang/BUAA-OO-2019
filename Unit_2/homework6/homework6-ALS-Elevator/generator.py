from xeger import Xeger
import time

def gererator():
    n = 6
    #regex = '^[1-9]-FROM-([1-9]|1[0-6])-TO-([1-9]|1[0-6])$'
    regex = '^-FROM-([1-9]|1[0-6])-TO-([1-9]|1[0-6])$'
    x = Xeger()

    with open('data.txt','w') as f1, open('datacheck_in.txt', 'w') as f2:
        for i in range(n):
            # time.sleep(0.7)
            s = str(i) + x.xeger(regex)    # get the regex str
            print(s)              
            data = s + '\n'
            data_std = '[0.0]' + data
            f1.write(data)
            f2.write(data_std)
            

def main(): 
    gererator()


if __name__ == '__main__':
    main()
