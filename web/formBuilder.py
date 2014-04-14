
class inputText :
    def __init__ (self, name) :
        self.name = name

    def html (self) :
        return '<input name=\"' + self.name + '\" />'

class inputSubmit :
    def __init__ (self, value) :
        self.value = value

    def html (self) :
        return '<input value="' + value + '" type="submit" />'

class FormBuilder :

    def __init__ (self, action) :
        self.elements = []
        self.action = action

    def add (self, text, field) :
        self.elements.append((text, field))

    def html () :
        result = '<table>'

        for element in elements :
            result += '<tr><td>' + element[0] + '</td><td>' + element[1].html() + '</td></tr'>

        return result += '</table>'