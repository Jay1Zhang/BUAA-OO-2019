from get_output import get_java_output
from get_output import get_std_output

Alterego = "java -Djava.ext.dirs=SixthPro/lib -classpath SixthPro/out/production/SixthPro/ Alterego.src.Main"
Archer = "java -Djava.ext.dirs=SixthPro/lib -classpath SixthPro/out/production/SixthPro/ Archer.src.homeworkvi.Main"
Assassin = "java -Djava.ext.dirs=SixthPro/lib -classpath SixthPro/out/production/SixthPro/ Assassin.src.oo_course_2019_16061139_homework_6.Test"
Berserker = "java -Djava.ext.dirs=SixthPro/lib -classpath SixthPro/out/production/SixthPro/ Berserker.src.MainClass"
Caster = "java -Djava.ext.dirs=SixthPro/lib -classpath SixthPro/out/production/SixthPro/ Caster.src.Main"
Lancer = "java -Djava.ext.dirs=SixthPro/lib -classpath SixthPro/out/production/SixthPro/ Lancer.src.Main"
Rider = "java -Djava.ext.dirs=SixthPro/lib -classpath SixthPro/out/production/SixthPro/ Rider.src.diantitwo.Test"
Saber = "java -Djava.ext.dirs=SixthPro/lib -classpath SixthPro/out/production/SixthPro/ Saber.src.Main"

# define command array
cmd_arr = [Alterego, Archer, Assassin, Berserker, Caster, Lancer, Rider, Saber]
# define output filename array
filename_arr = ['Alterego_output', 'Archer_output', 'Assassin_output', 'Berserke_output', 
                'Caster_output', 'Lancer_output', 'Rider_output', 'Saber_output']


def pat(sample_num:int):
    for k in range(sample_num):
        input = 'sample' + str(k) + '.txt'
        # get standard output
        output = 'standard_output_' + str(k) + '.txt'
        get_std_output(k, input, output)
        # get players output
        for i in range(8):
            command = cmd_arr[i]
            output = filename_arr[i] + '_' + str(k) + '.txt'
            get_java_output(command, input, output)
    
   

def main():
    pat(20)

if __name__ == '__main__':
    main()