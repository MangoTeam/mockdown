from dataclasses import dataclass, field
from itertools import chain
from more_itertools import take
from typing import Iterable, List, Set, Tuple
from dominate import tags as html


@dataclass
class Anchor:
    view: 'View'
    attribute: str
        
    @property
    def value(self):
        return getattr(self.view, self.attribute)
    
    def __repr__(self):
        return f"{self.view.name}.{self.attribute} @ {self.value}"

    
@dataclass
class Edge:
    anchor: Anchor
    interval: Tuple[int, int]
    
    @property
    def view(self) -> int:
        return self.anchor.view
    
    @property
    def attribute(self) -> int:
        return self.anchor.attribute
    
    @property
    def position(self) -> int:
        return self.anchor.value
    
    def __repr__(self):
        return f"{self.view.name}.{self.attribute} {self.interval} @ {self.position}"


@dataclass
class View:
    name: str
    rect: Tuple[int, int, int, int]
    children: List['View'] = field(default_factory=list)
        
    @property
    def left(self) -> int:
        return self.rect[0]
    
    @property
    def left_anchor(self) -> Anchor:
        return Anchor(self, 'left')
    
    @property
    def left_edge(self) -> Edge:
        return Edge(self.left_anchor, (self.top, self.bottom))
    
    @property
    def top(self) -> int:
        return self.rect[1]
    
    @property
    def top_anchor(self) -> Anchor:
        return Anchor(self, 'top')
    
    @property
    def top_edge(self) -> Edge:
        return Edge(self.top_anchor, (self.left, self.right))
    
    @property
    def right(self) -> int:
        return self.rect[2]

    @property
    def right_anchor(self) -> Anchor:
        return Anchor(self, 'right')
    
    @property
    def right_edge(self) -> Edge:
        return Edge(self.right_anchor, (self.top, self.bottom))
    
    @property
    def bottom(self) -> int:
        return self.rect[3]
    
    @property
    def bottom_anchor(self) -> Anchor:
        return Anchor(self, 'bottom')
    
    @property
    def bottom_edge(self) -> Edge:
        return Edge(self.bottom_anchor, (self.left, self.right))
    
    @property
    def center_x(self):
        return (self.left + self.right) / 2
    
    @property
    def center_x_anchor(self) -> Anchor:
        return Anchor(self, 'center_x')
    
    @property
    def center_y(self):
        return (self.top + self.bottom) / 2
    
    @property
    def center_y_anchor(self) -> Anchor:
        return Anchor(self, 'center_y')
    
    @property
    def width(self):
        return self.right - self.left
    
    @property
    def width_anchor(self) -> Anchor:
        return Anchor(self, 'width')
    
    @property
    def height(self):
        return self.bottom - self.top
    
    @property
    def height_anchor(self) -> Anchor:
        return Anchor(self, 'height')
    
    @property
    def anchor_labels(self):
        attrs = ["left", "right", 
                 "top", "bottom",
                 "center_x", "center_y",
                 "width", "height"]
        return [f"{self.name}.{attr}" for attr in attrs]
    
    def __iter__(self):
        yield self
        for v in chain(*map(iter, self.children)):
            yield v
    
    def _label_html(self):
        style = (
            "position: absolute;"
            "left: 5px;"
            "top: 5px;"
        )
        
        label = html.span(self.name, style=style)
        return label
    
    def to_html(self, scale=1):
        style = (
            "position: absolute;"
            "box-sizing: border-box;"
            "border: 1px solid black;"
            f"left:   {scale * self.left}px;"
            f"right:  {scale * self.right}px;"
            f"top:    {scale * self.top}px;"
            f"bottom: {scale * self.bottom}px;"
            f"height: {scale * self.height}px;"
            f"width:  {scale * self.width}px;"
        )
        
        div = html.div(id=self.name, style=style)
        div.add(self._label_html())
        
        return div
    
    def to_display_html(self, visible_pairs=[], scale=1):
        from .visibility import pair_to_html
        
        style = (
            "font-size: 10px;"
            "position: relative;"
            f"width:  {scale * self.width}px;"
            f"height: {scale * self.height}px;"
        )
        
        container = html.div(id="container", style=style)
        
        for view in self:
            container.add(view.to_html(scale=scale))
        
        for pair in visible_pairs:
            container.add(pair_to_html(pair, scale=scale))
        
        return container
