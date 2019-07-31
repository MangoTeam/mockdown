def horizontal_line_style(x0: int, x1: int, y: int, scale=1) -> str:
    if x0 > x1:
        x0, x1 = x1, x0
    return (f"left: {scale * x0}px;"
            f"right: {scale * x1}px;"
            f"top: {scale * y}px;"
            f"bottom: {scale * y}px;"
            f"width: {scale * (x1 - x0)}px;"
            "height: 1px;")


def vertical_line_style(y0: int, y1: int, x: int, scale=1) -> str:
    if y0 > y1:
        y0, y1 = y1, y0
    return (f"left: {scale * x}px;"
            f"right: {scale * x}px;"
            f"top: {scale * y0}px;"
            f"bottom: {scale * y1}px;"
            "width: 1px;"
            f"height: {scale * (y1 - y0)}px;")
