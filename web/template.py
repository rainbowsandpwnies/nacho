import re

TEMPLATE_PATH = 'templates/'

class Template :
    
    def __init__ (self) :
        self.templates = {}
        self.vars = {}

    def parse (self, template) :
        if template not in self.templates :
            fh = open(TEMPLATE_PATH + template, 'rb')
            self.templates[template] = fh.read()
            fh.close()

        template = self.templates[template]

        for key in self.vars :
            template = template.replace('{' + key + '}', self.vars[key])

        includes = re.findall("{include\.(.*?)}", template)
        for include in includes :
            template = template.replace('{include.' + include + '}', self.parse(include))

        return template

    def setvar (self, key, value) :
        self.vars[key] = value