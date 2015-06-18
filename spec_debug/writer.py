##  ===========================================================================
##  Author: Robert Koenighofer <robert.koenighofer@student.tugraz.at>
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

"""
Contains utility classes to print nice-to-read traces of signals.
"""

class Writer(object):
    """
    Helps to produce nice-to-read traces of signals.

    This module is able to collect actually chosen values and possible
    values for the different variables in the different time steps
    together. It transforms the collected data into a nice-to-read string
    and prints this string to STDOUT or to a file on demand.

    @author: Robert Koenighofer <robert.koenighofer@student.tugraz.at>
    @version: 1.0.0
    """
    def __init__(self, utils):
        """
        Constructor

        @param utils: A module containing a lot of utility-functions as
               well as data which is needed almost everywhere.
        @type utils: L{SpecDebugUtils}
        """

        #: A module containing a lot of utility-functions.
        #: @type: L{SpecDebugUtils}
        self.__utils = utils

        #: A dictionary for the content of the input variables.
        #:
        #: It maps from the input variable name to a two dimensional array of
        #: strings. The first dimension is the time step. The second dimension
        #: is either 0 or 1, 0 for the possible values, 1 for the actually
        #: chosen value.
        #: @type: dict<string,list<list<string>>>
        self.__content_in = {}

        #: A dictionary for the content of the output variables.
        #:
        #: It maps from the input variable name to a two dimensional array of
        #: strings. The first dimension is the time step. The second dimension
        #: is either 0 or 1, 0 for the possible values, 1 for the actually
        #: chosen value.
        #: @type: dict<string,list<list<string>>>
        self.__content_out = {}

        #: A dictionary for the content of the ix- and jx-variables.
        #:
        #: It maps from the input variable name to a two dimensional array of
        #: strings. The first dimension is the time step. The second dimension
        #: is either 0 or 1, 0 for the possible values, 1 for the actually
        #: chosen value.
        #: @type: dict<string,list<list<string>>>
        self.__content_aux = {}

        #: A counter counting the current time step
        #: @type: int
        self.__time_step = 0

        #: The time step from which the sequence is repeating
        #: @type: int
        self.__repeat_from = None

        #: The time step after which the sequence is repeating
        #: @type: int
        self.__repeat_to = None


    def clear(self):
        """
        Clears all data stored.
        """

        self.__content_in = {}
        self.__content_out = {}
        self.__content_aux = {}
        self.__time_step = 0
        self.__repeat_from = None
        self.__repeat_to = None

    def start_next_time_step(self):
        """
        Increases the time step counter.

        Setting possible or actual variable values only affects the value
        stored in the current time step.
        """

        self.__time_step += 1

    def set_possibilities(self, name, value):
        """
        Sets the possible values for an output variable.

        This method sets possible values for a specified output variable in
        the current time step.

        @param name: The name of the output variable.
        @type name: string
        @param value: A string containing the possible values for that
               output variable.
        @type value: string
        """

        # We perform the following operation:
        # self.__content_out[name][self__.time_step][0] = value
        if not (name in self.__content_out):
            self.__content_out[name] = []
        var_entry = self.__content_out[name]
        self.__utils.set_element_2d(var_entry, self.__time_step, 0, value)

    def set_chosen_input(self, name, value):
        """
        Sets the chosen value for an input variable.

        This method sets the actually chosen values for a specified input
        variable in the current time step.

        @param name: The name of the input variable.
        @type name: string
        @param value: A string containing the actually chosen value for
               that input variable.
        @type value: string
        """

        # We perform the following operation:
        # self.__content_in[name][self__.time_step][1] = value
        if not (name in self.__content_in):
            self.__content_in[name] = []
        var_entry = self.__content_in[name]
        self.__utils.set_element_2d(var_entry, self.__time_step, 1, value)

    def set_chosen_output(self, name, value):
        """
        Sets the chosen value for an output variable.

        This method sets the actually chosen values for a specified output
        variable in the current time step.

        @param name: The name of the output variable.
        @type name: string
        @param value: A string containing the actually chosen value for
               that output variable.
        @type value: string
        """

        # We perform the following operation:
        # self.__content_out[name][self__.time_step][1] = value
        if not (name in self.__content_out):
            self.__content_out[name] = []
        var_entry = self.__content_out[name]
        self.__utils.set_element_2d(var_entry, self.__time_step, 1, value)

    def set_chosen_aux(self, name, value):
        """
        Sets the chosen value for an ix- or jx-variable.

        This method sets the actually chosen values for a specified ix- or jx-
        variable in the current time step.

        @param name: The name of the ix- or jx-variable.
        @type name: string
        @param value: A string containing the actually chosen value for
               that ix- or jx-variable.
        @type value: string
        """

        # We perform the following operation:
        # self.__content_aux[name][self__.time_step][1] = value
        if not (name in self.__content_aux):
            self.__content_aux[name] = []
        var_entry = self.__content_aux[name]
        self.__utils.set_element_2d(var_entry, self.__time_step, 1, value)

    def set_repeat_indices(self, repeat_from, repeat_to):
        """
        Sets the time steps between which the sequence of signals repeats.

        @param repeat_from: The time step from which the sequence is
               repeating.
        @type repeat_from: int
        @param repeat_to: The time step after which the sequence is
               repeating.
        @type repeat_to: int
        """

        self.__repeat_from = repeat_from
        self.__repeat_to = repeat_to

    def print_to_stdout(self):
        """
        Prints the collected data to STDOUT.

        This method computes a nice-to-read string representation of all the
        collected data and prints it to STDOUT.
        """
        print self.toString()

    def write_to_file(self, filename):
        """
        Prints the collected data into a file.

        This method computes a nice-to-read string representation of all the
        collected data and prints it to a file (appends the new data).

        @param filename: The name of the file (including path) to write to.
        @type filename: string
        """
        file = open(filename, 'a')
        file.write(self.to_string())
        file.close()

    def to_string(self):
        """
        Returns the collected data as string.

        This method computes a nice to read string representation of all the
        collected data and returns this string.

        @return: A string representation of all the collected data.
        @rtype: string
        """
        result_string = "\n\n"
        result_string += self._print_hline()
        result_string += self._print_header()
        result_string += self._print_hline()
        result_string += self._table_to_string(self.__content_in)
        result_string += self._table_to_string(self.__content_out)
        result_string += self._table_to_string(self.__content_aux)
        result_string += self._print_hline()
        if self.__repeat_from and self.__repeat_to:
            result_string += self.print_repeat(self.__repeat_from, \
                                               self.__repeat_to)
            result_string += self._print_hline()
        return result_string

    def _table_to_string(self, table):
        """
        Transforms one of the tables into a string.

        This method computes a nice-to-read string representation of one of
        the tables of this module (content_in, content_out or content_aux)
        and returns this string.

        @param table: The table to transform.
        @type table: dict<string,list<list<string>>>
        @return: A string representation of the table.
        @rtype: string
        """

        result_string = ""

        for entry_name in table.keys():
            result_string += entry_name
            spaces = 20 - len(entry_name)
            result_string += " " * spaces
            result_string += "| "
            for i in range(0, self.__time_step + 1):
                if len(table[entry_name]) > i and \
                   len(table[entry_name][i]) > 0 and \
                   table[entry_name][i][0]:
                    result_string += str(table[entry_name][i][0])
                    result_string += ":"
                else:
                    result_string += "      "
            
                if len(table[entry_name]) > i and \
                   len(table[entry_name][i]) > 1 and \
                   table[entry_name][i][1]:
                    result_string += str(table[entry_name][i][1])
                else:
                    result_string += " "
            
                result_string += " | "
            result_string += "\n"
        result_string += "\n"
        return result_string


    def _print_header(self):
        """
        Returns a header for the table.

        This method returns a string containing the header line of the table
        summarizing all signals in all time steps. The header line contains
        the time steps.

        @return: A string representation of the header line.
        @rtype: string
        """

        result_string = "Variable Name       | "

        for i in range(0, self.__time_step + 1):
            result_string += ("step %02d | " % i)
        
        result_string += "\n"
        return result_string

    def _print_hline(self):
        """
        Returns a horizontal line in the table.
        
        @return: A string representing a horizontal line in the table.
        @rtype: string
        """
        len = 22 + (10 * (self.__time_step + 1));
        return "_" * len + "\n";


    def print_repeat(self, from_step, to_step):
        """
        Returns a string that shows how the sequence of signals repeats.

        A fine piece of ASCII-Art. GUIs suck ;-)

        @return: A string that shows how the sequence of signals repeats.
        @rtype: string
        """

        result_string = "Repeating this      | "
        for i in range(0, self.__time_step + 1):
            if i == from_step and i == to_step:
                result_string += "/ \\    |  "
            elif i == from_step:
                result_string += "   / \\    "
            elif i == to_step:
                result_string += "    |     "
            else:
                result_string += "          "
        result_string += "\nway:                | ";
        for i in range(0, self.__time_step + 1):
            if i == from_step and i == to_step:
                result_string += " |_____|  "
            elif i == from_step:
                result_string += "    |_____"
            elif i == to_step:
                result_string += "____|     "
            elif i < to_step and i > from_step:
                result_string += "__________"
            else:
                result_string += "          "
        
        result_string += "\n"
        return result_string
