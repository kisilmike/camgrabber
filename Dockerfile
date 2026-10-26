FROM python:3.12-alpine
RUN apk add --no-cache tzdata
ENV TZ=Europe/Moscow PYTHONUNBUFFERED=1
WORKDIR /app
RUN pip install --no-cache-dir pillow==10.4.0
COPY app/grabber.py app/cam_page.html app/settings.html /app/
HEALTHCHECK --interval=60s --timeout=5s --retries=3 CMD ["python", "/app/grabber.py", "health"]
CMD ["python", "/app/grabber.py", "run"]
