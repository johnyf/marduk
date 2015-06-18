#!/usr/bin/env python


##  ===========================================================================
##  Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
##
##  Copyright (c) 2009, 2010 by Graz University of Technology 
##
##  This is free software; you can redistribute it and/or
##  modify it under the terms of the GNU Lesser General Public
##  License as published by the Free Software Foundation; either
##  version 2 of the License, or (at your option) any later version.
##
##  This software is distributed in the hope that it will be useful,
##  but WITHOUT ANY WARRANTY; without even the implied warranty of
##  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
##  Lesser General Public License for more details.
##
##  You should have received a copy of the GNU Lesser General Public
##  License along with this library; if not, write to the Free Software
##  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307  USA.
##
##  For more information about this software see <http://rat.fbk.eu/ratsy>
##  or email to the RATSY Team <ratsy@list.fbk.eu>.
##  Please report bugs to <ratsy@list.fbk.eu>.
##
##  ===========================================================================



# This file contains a utility program to create a table with
# synthesis results from log files stored in a directory.
# Log files are assumed to have .log extension.
# ABC Log files are assumed to have a .abc extension. This can
# be changed by command-line flags.



from optparse import OptionParser
import re
import os
import sys
import math


def to_hhmmss(value):
    seconds = '%5.2f' % (value  % 60)
    seconds = re.sub(' ', '0', seconds)

    minutes = (value / 60) % 60
    if minutes < 10:
        minutes = '0' + '%d' % minutes
    else:
        minutes = '%d' % minutes

    hours = math.floor(value / 3600)
    if hours < 10:
        hours = '0' + '%d' % hours
    else:
        hours = '%d' % hours

    return '%s:%s:%s' % (hours, minutes, seconds)
    


def write_output(file_name, table, mode):

    if mode.lower() == 'twiki':
        write_twiki(file_name, table)
    elif mode.lower() == 'csv':
        write_csv(file_name, table)
    elif mode.lower() == 'html':
        write_html(file_name, table)


def write_twiki(file_name, table):
    if not file_name:
        file = sys.stdout
    else:
        file = open(file_name, 'w')

    file.write('| * * ')
    for elem in table:
        file.write('| *%s* ' % elem[0])
    file.write('|\n')

    file.write('| *Total Time* ')
    for elem in table:
        file.write('|  %7.2f ' % elem[1]['overall'])
    file.write('|\n')

    file.write('| *Total Time (HH:MM:SS)* ')
    for elem in table:
        file.write('|  %s ' % to_hhmmss(elem[1]['overall']))
    file.write('|\n')

    file.write('| *Wall Clock Time* ')
    for elem in table:
        if elem[1].has_key('wall_clock'):
            file.write('|  %7.2f ' % elem[1]['wall_clock'])
        else:
            file.write('|  --- ')
    file.write('|\n')

    file.write('| *Wall Clock Time (HH:MM:SS)* ')
    for elem in table:
        if elem[1].has_key('wall_clock'):
            file.write('|  %s ' % to_hhmmss(elem[1]['wall_clock']))
        else:
            file.write('|  --- ')
    file.write('|\n')

    file.write('| *Time for Winning Region* ')
    for elem in table:
        file.write('|  %7.2f ' % elem[1]['winreg'])
    file.write('|\n')

    file.write('| *Time for Strategy* ')
    for elem in table:
        file.write('|  %7.2f ' % elem[1]['strategy'])
    file.write('|\n')

    file.write('| *Time for Output Functions* ')
    for elem in table:
        file.write('|  %7.2f ' % elem[1]['output_functions'])
    file.write('|\n')

    file.write('| *Second Reordering* ')
    for elem in table:
        file.write('|  %7.2f ' % elem[1]['second_reorder'])
    file.write('|\n')
    
    file.write('| *Killing* ')
    for elem in table:
        file.write('|  %7.2f ' % elem[1]['killing'])
    file.write('|\n')

    file.write('| *Transferring Functions* ')
    for elem in table:
        if elem[1].has_key('transfer'):
            file.write('|  %7.2f ' % elem[1]['transfer'])
        else:
            file.write('|  --- ')
    file.write('|\n')

    file.write('| *Reorder Transferred* ')
    for elem in table:
        if elem[1].has_key('reorder_transferred'):
            file.write('|  %7.2f ' % elem[1]['reorder_transferred'])
        else:
            file.write('|  --- ')
    file.write('|\n')
    
    file.write('| *Area before ABC* ')
    for elem in table:
        if elem[2].has_key('before'):
            file.write('|  %7.2f ' % elem[2]['before'])
        else:
            file.write('|  ')
    file.write('|\n')

    file.write('| *Area after ABC* ')
    for elem in table:
        if elem[2].has_key('after'):
            file.write('|  %7.2f ' % elem[2]['after'])
        else:
            file.write('|  ')
    file.write('|\n')
        
    file.close()
    
def write_csv(file_name, table):
    if not file_name:
        file = sys.stdout
    else:
        file = open(file_name, 'w')

    file.write('  ')
    for elem in table:
        file.write('; %s ' % elem[0])
    file.write(';\n')

    file.write('Total Time ')
    for elem in table:
        file.write(';  %7.2f ' % elem[1]['overall'])
    file.write(';\n')

    file.write('Total Time (HH:MM:SS) ')
    for elem in table:
        file.write(';  %s ' % to_hhmmss(elem[1]['overall']))
    file.write(';\n')

    file.write('Wall Clock Time ')
    for elem in table:
        if elem[1].has_key('wall_clock'):
            file.write(';  %7.2f ' % elem[1]['wall_clock'])
        else:
            file.write(';  --- ')
    file.write(';\n')

    file.write('Wall Clock Time (HH:MM:SS) ')
    for elem in table:
        if elem[1].has_key('wall_clock'):
            file.write(';  %s ' % to_hhmmss(elem[1]['wall_clock']))
        else:
            file.write(';  --- ')
    file.write(';\n')

    file.write('Time for Winning Region ')
    for elem in table:
        file.write(';  %7.2f ' % elem[1]['winreg'])
    file.write(';\n')

    file.write('Time for Strategy ')
    for elem in table:
        file.write(';  %7.2f ' % elem[1]['strategy'])
    file.write(';\n')

    file.write('Time for Output Functions ')
    for elem in table:
        file.write(';  %7.2f ' % elem[1]['output_functions'])
    file.write(';\n')

    file.write('Second Reordering ')
    for elem in table:
        file.write(';  %7.2f ' % elem[1]['second_reorder'])
    file.write(';\n')
    
    file.write('Killing ')
    for elem in table:
        file.write(';  %7.2f ' % elem[1]['killing'])
    file.write(';\n')

    file.write('Transferring Functions ')
    for elem in table:
        if elem[1].has_key('transfer'):
            file.write(';  %7.2f ' % elem[1]['transfer'])
        else:
            file.write(';  --- ')
    file.write(';\n')

    file.write('Reorder Transferred ')
    for elem in table:
        if elem[1].has_key('reorder_transferred'):
            file.write(';  %7.2f ' % elem[1]['reorder_transferred'])
        else:
            file.write(';  --- ')
    file.write(';\n')
    
    file.write('Area before ABC ')
    for elem in table:
        if elem[2].has_key('before'):
            file.write(';  %7.2f ' % elem[2]['before'])
        else:
            file.write(';  ')
    file.write(';\n')

    file.write('Area after ABC ')
    for elem in table:
        if elem[2].has_key('after'):
            file.write(';  %7.2f ' % elem[2]['after'])
        else:
            file.write(';  ')
    file.write(';\n')
        
    file.close()

    
def write_html(file_name, table):
    if not file_name:
        file = sys.stdout
    else:
        file = open(file_name, 'w')

    file.write('<table>\n\n<tr>\n<th></th>\n')
    for elem in table:
        file.write('<th>%s</th>' % elem[0])
    file.write('\n</tr>\n\n')

    file.write('<tr>\n<th>Total Time</th>')
    for elem in table:
        file.write('<td>%7.2f</td>' % elem[1]['overall'])
    file.write('\n</tr>\n\n')

    file.write('<tr>\n<th>Total Time (HH:MM:SS)</th>')
    for elem in table:
        file.write('<td>%s</td>' % to_hhmmss(elem[1]['overall']))
    file.write('\n</tr>\n\n')

    file.write('<tr>\n<th>Wall Clock Time</th>')
    for elem in table:
        if elem[1].has_key('wall_clock'):
            file.write('<td>%7.2f</td>' % elem[1]['wall_clock'])
        else:
            file.write('<td> ---</td>')
    file.write('\n</tr>\n\n')

    file.write('<tr>\n<th>Wall Clock Time (HH:MM:SS)</th>')
    for elem in table:
        if elem[1].has_key('wall_clock'):
            file.write('<td>%s</td>' % to_hhmmss(elem[1]['wall_clock']))
        else:
            file.write('<td> ---</td>')
    file.write('\n</tr>\n\n')    
    
    file.write('<tr>\n<th>Time for Winning Region</th>')
    for elem in table:
        file.write('<td>%7.2f</td>' % elem[1]['winreg'])
    file.write('\n</tr>\n\n')

    file.write('<tr>\n<th>Time for Strategy</th>')
    for elem in table:
        file.write('<td>%7.2f</td>' % elem[1]['strategy'])
    file.write('\n</tr>\n\n')

    file.write('<tr>\n<th>Time for Output Functions</th>')
    for elem in table:
        file.write('<td>%7.2f</td>' % elem[1]['output_functions'])
    file.write('\n</tr>\n\n')

    file.write('<tr>\n<th>Second Reordering</th>')
    for elem in table:
        file.write('<td>%7.2f</td>' % elem[1]['second_reorder'])
    file.write('\n</tr>\n\n')
    
    file.write('<tr>\n<th>Killing</th>')
    for elem in table:
        file.write('<td>%7.2f</td>' % elem[1]['killing'])
    file.write('\n</tr>\n\n')

    file.write('<tr>\n<th>Transferring Functions</th>')
    for elem in table:
        if elem[1].has_key('transfer'):
            file.write('<td>%7.2f</td>' % elem[1]['transfer'])
        else:
            file.write('<td>---</td>')
    file.write('\n</tr>\n\n')

    file.write('<tr>\n<th>Reorder Transferred</th>')
    for elem in table:
        if elem[1].has_key('reorder_transferred'):
            file.write('<td>%7.2f</td>' % elem[1]['reorder_transferred'])
        else:
            file.write('<td>---</td>')
    file.write('\n</tr>\n\n')
    
    file.write('<tr>\n<th>Area before ABC</th>')
    for elem in table:
        if elem[2].has_key('before'):
            file.write('<td>%7.2f</td>' % elem[2]['before'])
        else:
            file.write('<td></td>')
    file.write('\n</tr>\n\n')

    file.write('<tr>\n<th>Area after ABC</th>')
    for elem in table:
        if elem[2].has_key('after'):
            file.write('<td>%7.2f</td>' % elem[2]['after'])
        else:
            file.write('<td></td>')
    file.write('\n</tr>\n\n')
    file.write('</table>\n')    
    file.close()
    

def get_log_info(file_name):
    file = open(file_name,'r')
    lines = file.readlines()
    file.close()

    info = {'winreg':float("NaN"),
            'strategy':float("NaN"),
            'output_functions':float("NaN"),
            'second_reorder':float("NaN"),
            'killing':float("NaN"),
            'overall':float("NaN")}
    for line in lines:
        if re.search('Compute winning region', line):
            match = re.search(r'(\d+\.\d+)', line)
            info['winreg'] = float(match.group(1))  
        elif re.search('Compute strategy', line):
            match = re.search(r'(\d+\.\d+)', line)
            info['strategy'] = float(match.group(1))          
        elif re.search('Compute output functions', line):
            match = re.search(r'(\d+\.\d+)', line)
            info['output_functions'] = float(match.group(1))
        elif re.search('Second reordering', line):
            match = re.search(r'(\d+\.\d+)', line)
            info['second_reorder'] = float(match.group(1))
        elif re.search('Killing', line):
            match = re.search(r'(\d+\.\d+)', line)
            info['killing'] = float(match.group(1))
        elif re.search('Transferred output functions', line):
            match = re.search(r'(\d+\.\d+)', line)
            info['transfer'] = float(match.group(1))
        elif re.search('Reordering transferred', line):
            match = re.search(r'(\d+\.\d+)', line)
            info['reorder_transferred'] = float(match.group(1))
        elif re.search('overall time', line):
            match = re.search(r'(\d+\.\d+)', line)
            info['overall'] = float(match.group(1))
        elif re.search('wall clock time', line):
            match = re.search(r'(\d+\.\d+)', line)
            info['wall_clock'] = float(match.group(1))
                
             
    return info

def get_abc_info(file_name):
    file = open(file_name,'r')
    lines = file.readlines()
    file.close()

    info = {}
    for line in lines:
        if re.search('area = ', line):
            if not info.has_key('before'):
                match = re.search(r'area =\D*(\d+\.\d+)', line)
                info['before'] = float(match.group(1))  
        elif re.search(r'TOTAL.+Area =\w*', line):
            #print "Line:"
            #print line
            match = re.search(r'TOTAL.+Area =\D*(\d+\.\d+)', line)
            #print match
            info['after'] = float(match.group(1))          
    return info

###########################################################################
#
# Start of main routine

parser = OptionParser()

parser.add_option("-d", "--directory", dest="directory", default="",
                  help="The directory to search for log files.")

parser.add_option("--log-extension", dest="log_extension", default=".log",
                  help="The extension of log files to search.")

parser.add_option("--abc-extension", dest="abc_extension", default=".abc",
                  help="The extension of abc log-files to search.")

parser.add_option("-f", "--file", dest="file",
                  help="The filename to write the output to. If none is given, stdout is used.")

parser.add_option("-m", "--mode", dest="mode", default="twiki",
                  help="Output mode. Allowed values are 'twiki' (default), 'csv', 'html'")

parser.add_option("--max", dest="max", type="int",
                  help="Maximum number of files to process.")

(options, args) = parser.parse_args();

if options.max:
    if options.max < 1:
        print "ERROR: Invalid option '--max %d'!" % options.max
        exit(-1)

if not os.path.isdir(options.directory):
    print "ERROR: '%s' does not exist or is not a directory!" % options.directory
    exit(-1)

files = os.listdir(options.directory)
files.sort()

if len(files) == 0:
    print "ERROR: %s is empty!" % options.directory
    exit(-1)

log_files = [file for file in files if re.search(re.sub(r'\.',r'\.',options.log_extension) + '$', file)]
if options.max:
    log_files = log_files[0:min(options.max, len(log_files))]

if len(log_files) == 0:
    print "ERROR: %s contains no log files!" % options.directory
    exit(-1)


table = []        
for i in range(0, len(log_files)):
    name = re.sub(options.log_extension + '$', '', log_files[i])
    abc_file_name = re.sub(options.log_extension + '$', options.abc_extension, log_files[i])
    if not os.path.exists(os.path.join(options.directory, abc_file_name)):
        print "WARNING: No abc log file for '%s'! abc info will be skipped!" % (log_files[i])
        abc_info = {}
    else:
        abc_info = get_abc_info(os.path.join(options.directory, abc_file_name))
        
    log_info = get_log_info(os.path.join(options.directory, log_files[i]))

    table.append((name, log_info, abc_info))
                   

write_output(options.file, table, options.mode)
exit(0)
